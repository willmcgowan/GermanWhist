#include <algorithm>
#include <string>
#include <array>
#include <iostream>
#include <chrono>
#include <cassert>
#include <random>
#include <vector>
#include <intrin.h>
//#define DEBUG


//unusual suit ranking is due to endgame solver implementation.
const int kChancePlayerId = -1;
const int kNumSuits = 4;
const int kNumRanks = 13;
constexpr char kRankChar[] = "AKQJT98765432";
constexpr char kSuitChar[] = "CDHS";

const std::array<uint64_t, 4> kSuitMasks = { _bzhi_u64(~0,kNumRanks),_bzhi_u64(~0,2 * kNumRanks) ^ _bzhi_u64(~0,kNumRanks),_bzhi_u64(~0,3 * kNumRanks) ^ _bzhi_u64(~0,2 * kNumRanks),_bzhi_u64(~0,4 * kNumRanks) ^ _bzhi_u64(~0,3 * kNumRanks) };


typedef int Player;
typedef int Action;
using ActionsAndProbs = std::vector<std::pair<Action, double>>;
struct PlayerAction {
	Player player;
	Action action;
	bool operator==(const PlayerAction&) const;
};
inline int CardRank(int card, int suit) { 
	uint64_t card_mask = ((uint64_t)1 << card);
	card_mask = (card_mask >> (suit * kNumRanks));
	return _tzcnt_u64(card_mask);
}
inline int CardSuit(int card) {
	uint64_t card_mask = ((uint64_t)1 << card);
	for (int i = 0; i < kNumSuits; ++i) {
		if (__popcnt64(card_mask & kSuitMasks[i]) == 1) {
			//std::cout << "Hello" << std::endl;
			return i;
		}
	}
	return kNumSuits;
}
std::string CardString(int card) {
	int suit = CardSuit(card);
	return { kSuitChar[suit],kRankChar[CardRank(card,suit)] };
}


class GWhistState {
private:
	uint64_t deck_;//coordinate x of holder_ denotes who holds card x -1 = deck_ 0,1 = players, 2 = discard//;
	uint64_t discard_;
	std::array<uint64_t, 2> hands_;
	std::vector<PlayerAction> history_;
	int moves_;
	int player_;
	int trump_;
public:
	GWhistState() {
		player_ = kChancePlayerId;
		moves_ = 0;
		trump_ = -1;
		deck_ = _bzhi_u64(~0,kNumRanks*kNumSuits);
		discard_ = 0;
		hands_ = { 0,0 };
		history_.reserve(78);
	}
	GWhistState(const GWhistState& state) {
		//copy constructor//
		player_ = state.player_;
		moves_ = state.moves_;
		trump_ = state.trump_;
		deck_ = state.deck_;
		discard_ = state.discard_;
		hands_ = state.hands_;
		history_ = state.history_;
	}
	bool Trick(int lead, int follow) {
		int lead_suit = CardSuit(lead);
		int follow_suit = CardSuit(follow);
		int lead_rank = CardRank(lead,lead_suit);
		int follow_rank = CardRank(follow,follow_suit);
		return (lead_suit == follow_suit && lead_rank < follow_rank) || (lead_suit != follow_suit && follow_suit != trump_);
	}
	bool IsTerminal() const {
		return(__popcnt64(deck_) == 0);
	}

	bool IsChanceNode() const { return player_ == kChancePlayerId; }

	int CurrentPlayer() const { return player_; }
	int Moves() const { return moves_; }

	std::vector<std::pair<Action, double>> ChanceOutcomes() const {
		std::vector<std::pair<Action, double>> outcomes;
		return outcomes;
	}
	std::string ActionToString(Player player, Action move) const {
		return std::to_string(player) + " " + CardString(move) + "\n";
	}
	std::string ToString() {
		std::string out;
		for (int i = 0; i < history_.size(); ++i) {
			out += ActionToString(history_[i].player, history_[i].action);
		}
		return out;
	}
	std::string StateToString() {
		//doesnt use history in case of a resampled state with unreconciled history//
		std::string out;
		uint64_t copy_deck = deck_;
		uint64_t copy_discard = discard_;
		std::array<uint64_t,2> copy_hands = hands_;
		std::vector<int> deck_cards;
		std::vector<int> player0_cards;
		std::vector<int> player1_cards;
		std::vector<int> discard;
		while (copy_deck != 0) {
			deck_cards.push_back(_tzcnt_u64(copy_deck));
			copy_deck = _blsr_u64(copy_deck);
		}
		while (copy_discard != 0) {
			discard.push_back(_tzcnt_u64(copy_discard));
			copy_discard = _blsr_u64(copy_discard);
		}

		while (copy_hands[0] != 0) {
			player0_cards.push_back(_tzcnt_u64(copy_hands[0]));
			copy_hands[0] = _blsr_u64(copy_hands[0]);
		}
		while (copy_hands[1] != 0) {
			player1_cards.push_back(_tzcnt_u64(copy_hands[1]));
			copy_hands[1] = _blsr_u64(copy_hands[1]);
		}
		out += "Deck \n";
		for (int i = 0; i < deck_cards.size(); ++i) {
			out += CardString(deck_cards[i]) + "\n";
		}
		out += "Discard \n";
		for (int i = 0; i < discard.size(); ++i) {
			out += CardString(discard[i]) + "\n";
		}

		for (int i = 0; i < 2; ++i) {
			out += "Player " + std::to_string(i) + "\n";
			std::vector<int> var;
			if (i == 0) {
				var = player0_cards;
			}
			else {
				var = player1_cards;
			}
			for (int j = 0; j < var.size(); ++j) {
				out += CardString(var[j]) + "\n";
			}
		}
		return out;
	}
	std::vector<Action> LegalActions() const{
		std::vector<Action> actions;
		if (IsTerminal()) return {};
		if (IsChanceNode()) {
			actions.reserve(__popcnt64(deck_));
			uint64_t copy_deck = deck_;
			while (copy_deck != 0) {
				actions.push_back(_tzcnt_u64(copy_deck));
				copy_deck = _blsr_u64(copy_deck);
			}
		}
		else {
			//lead//
			actions.reserve(kNumRanks);
			if (history_.back().player == kChancePlayerId) {
				uint64_t copy_hand = hands_[player_];
				while (copy_hand != 0) {
					actions.push_back(_tzcnt_u64(copy_hand));
					copy_hand = _blsr_u64(copy_hand);
				}
			}

			//follow//
			else {
				uint64_t copy_hand = hands_[player_] & kSuitMasks[CardSuit(history_.back().action)];
				if (copy_hand == 0) {
					copy_hand = hands_[player_];
				}
				while (copy_hand != 0) {
					actions.push_back(_tzcnt_u64(copy_hand));
					copy_hand = _blsr_u64(copy_hand);
				}
			}
		}
		return actions;
	}

	void DoApplyAction(Action move) {
		// Additional book-keeping
		//initial deal//
		int player_start = player_;
		if (moves_ < (kNumSuits * kNumRanks) / 2) {
			hands_[moves_ % 2] = (hands_[moves_ % 2] |((uint64_t)1 << move));
			deck_ = (deck_ ^ ((uint64_t)1 << move));
		}
		else if (moves_ == (kNumSuits * kNumRanks / 2)) {
			trump_ = CardSuit(move);
			deck_ = (deck_ ^ ((uint64_t)1 << move));
			player_ = 0;
		}
		//cardplay//
		else if (moves_ > (kNumSuits * kNumRanks) / 2) {
			int move_index = (moves_ - ((kNumSuits * kNumRanks) / 2)) % 4;
			switch (move_index) {
				bool lead_win;
				int winner;
				int loser;
			case 0:
				//revealing face up card//
				deck_ = (deck_ ^ ((uint64_t)1 << move));
				lead_win = Trick(history_[moves_ - 3].action, history_[moves_ - 2].action);
				winner = ((lead_win) ^ (history_[moves_ - 3].player == 0)) ? 1 : 0;
				player_ = winner;
				break;
			case 1:
				//establishing lead//
				discard_ = (discard_|((uint64_t)1<<move));
				hands_[player_] = (hands_[player_] ^ ((uint64_t)1 << move));
				(player_ == 0) ? player_ = 1 : player_ = 0;
				break;
			case 2:
				//following and awarding face up//
				discard_ = (discard_ | ((uint64_t)1 << move));
				hands_[player_] = (hands_[player_] ^ ((uint64_t)1 << move));
				lead_win = Trick(history_[moves_ - 1].action, move);
				winner = ((lead_win) ^ (history_[moves_ - 1].player == 0)) ? 1 : 0;
				hands_[winner] = (hands_[winner] | ((uint64_t)1 << history_[moves_ - 2].action));
				player_ = kChancePlayerId;
				break;
			case 3:
				//awarding face down//
				deck_ = (deck_ ^ ((uint64_t)1 << move));
				lead_win = Trick(history_[moves_ - 2].action, history_[moves_ - 1].action);
				loser = ((lead_win) ^ (history_[moves_ - 2].player == 0)) ? 0 : 1;
				hands_[loser] = (hands_[loser] | ((uint64_t)1 << move));
				break;
			}
		}
#ifdef DEBUG
		std::cout << ActionToString(player_start, move) << std::endl;
		std::cout << move << std::endl;
#endif
		history_.push_back(PlayerAction{ player_start,move });
		moves_++;
	}
	GWhistState ResampleFromInfoState(Player player,std::mt19937 &gen) {
		//only valid when called from a position where a player can act//
		//to fix, the most recent face up card cannot be in opponents hand even though its been seen and isnt in our hand or discard unless the most recent face up card has been claimed//
		GWhistState resampled_state(*this);
		uint64_t necessary_cards = 0;
		for (int i = 2 * kNumRanks; i < history_.size(); i+=4) {
			//face up cards from deck//
			necessary_cards = (necessary_cards | (uint64_t(1) << history_[i].action));
		}
		int move_index = moves_ - ((kNumRanks * kNumSuits) / 2);
		int move_remainder = move_index % 4;
		int opp = (player == 0) ? 1 : 0;
		int recent_faceup = moves_ - move_remainder;
		uint64_t recent_faceup_card = (uint64_t(1) << history_[recent_faceup].action);
		// if a face up card from the deck is not in players hand or discard it must be in opps unless it is the most recent face up//
		necessary_cards = (necessary_cards & (~(hands_[player] | discard_|recent_faceup_card)));
		//sufficient cards are all cards not in players hand,the discard, or the recent face up//
		uint64_t sufficient_cards = (_bzhi_u64(~0, kNumRanks * kNumSuits) &(~(hands_[player] | discard_|recent_faceup_card)));
		//sufficient_cards are not necessary //
		sufficient_cards = (sufficient_cards & (~(necessary_cards)));
		//we must now take into account the observation of voids//
		std::array<int, kNumSuits> when_voided = {0,0,0,0};
		std::array<int, kNumSuits> voids = {-1,-1,-1,-1};
		std::vector<int> opp_dealt_hidden;
		for (int i = 2 * kNumRanks; i < history_.size(); ++i) {
			if (history_[i - 1].player == player && history_[i].player == (opp) && CardSuit(history_[i-1].action)!=CardSuit(history_[i].action)) {
				when_voided[CardSuit(history_[i - 1].action)] = i - 1;
			}
			if (history_[i - 1].player == player && history_[i].player == (opp) && Trick(history_[i - 1].action, history_[i].action)) {
				opp_dealt_hidden.push_back(i - 1);
			}
			if (history_[i - 1].player == (opp) && history_[i].player == (player) && !Trick(history_[i - 1].action, history_[i].action)) {
				opp_dealt_hidden.push_back(i - 1);
			}
		}
		//now voids contains the number of hidden cards dealt to opp since it showed a void in that suit, i.e the maximum number of cards held in that suit//
		//if the suit is unvoided, then this number is -1//
		for (int i = 0; i < kNumSuits; ++i) {
			if (when_voided[i] != 0) {
				voids[i] = 0;
				for (int j = 0; j < opp_dealt_hidden.size(); ++j) {
					if (opp_dealt_hidden[j] >= when_voided[i]) {
						voids[i] += 1;
					}
				}
			}
		}
		//we now perform a sequence of shuffles to generate a possible opponent hand, and make no attempt to reconcile the history with this new deal//
		int nec = __popcnt64(necessary_cards);
		for (int i = 0; i < kNumSuits; ++i) {
			if (voids[i] != -1&&__popcnt64(sufficient_cards&kSuitMasks[i])>voids[i]) {
				uint64_t suit_subset = (sufficient_cards & kSuitMasks[i]);
				std::vector<int> temp;
				while (suit_subset != 0) {
					temp.push_back(_tzcnt_u64(suit_subset));
					suit_subset = _blsr_u64(suit_subset);
				}
				std::shuffle(temp.begin(), temp.end(), gen);
				sufficient_cards = (sufficient_cards &~(kSuitMasks[i]));
				for (int j = 0; j < voids[i]; ++j) {
					sufficient_cards = (sufficient_cards | (uint64_t(1) << temp[j]));
				}
			} 
		}
		//finally generating a possible hand for opponent//
		std::vector<int> hand_vec;
		while (sufficient_cards != 0) {
			hand_vec.push_back(_tzcnt_u64(sufficient_cards));
			sufficient_cards = _blsr_u64(sufficient_cards);
		}
		std::shuffle(hand_vec.begin(), hand_vec.end(), gen);
		uint64_t opp_hand=0;
		for (int i = 0; i < __popcnt64(hands_[opp])-nec; ++i) {
			opp_hand = opp_hand | (uint64_t(1) << hand_vec[i]);
		}
		opp_hand = opp_hand | necessary_cards;
		resampled_state.hands_[!player] = opp_hand;
		resampled_state.deck_ = _bzhi_u64(~0, kNumRanks * kNumSuits) ^ (discard_ | opp_hand | hands_[player]|recent_faceup_card);
		return resampled_state;
	}

	std::vector<double> Returns() {
		return std::vector<double>(2, 0);
	}
};
