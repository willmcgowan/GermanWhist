#include <vector>
#include <algorithm>
#include <string>
#include <array>
#include <iostream>
#include <chrono>
#include <cassert>
#include <random>
#include <vector>
//#define DEBUG
//number of cards must be divisible by 4//
const int kChancePlayerId = -1;
const int kNumSuits = 4;
const int kNumRanks = 13;
constexpr char kRankChar[] = "23456789TJQKA";
constexpr char kSuitChar[] = "CDHS";


typedef int Player;
typedef int Action;
using ActionsAndProbs = std::vector<std::pair<Action, double>>;
struct PlayerAction {
	Player player;
	Action action;
	bool operator==(const PlayerAction&) const;
};
int CardRank(int card, int num_suits) { return card/num_suits; }
int CardSuit(int card, int num_suits) {return card%num_suits; }
std::string CardString(int card,int num_suits) {
	return { kSuitChar[(CardSuit(card,num_suits))],
			kRankChar[CardRank(card,num_suits)]};
}


class GWhistState{
private:
	std::vector<int> holder_;//coordinate x of holder_ denotes who holds card x -1 = deck_ 0,1 = players, 2 = discard//;
	std::vector<PlayerAction> history_;
	int moves_;
	int player_;
	int num_suits_;
	int num_ranks_;
	int trump_;
public:
	GWhistState(int num_suits, int num_ranks) {
		player_ = kChancePlayerId;
		num_suits_ = num_suits;
		num_ranks_ = num_ranks;
		moves_ = 0;
		trump_ = -1;
		holder_=std::vector<int>(num_suits*num_ranks,-1);
	}
	bool Trick(int lead, int follow) {
		int lead_suit = CardSuit(lead, num_suits_);
		int follow_suit = CardSuit(follow, num_suits_);
		int lead_rank = CardRank(lead, num_suits_);
		int follow_rank = CardRank(follow, num_suits_);
		return (lead_suit == follow_suit && lead_rank > follow_rank) || (lead_suit != follow_suit &&follow_suit!= trump_);
	}
	bool IsTerminal() {
		int sum = 0;
		for (int i = 0; i < holder_.size(); ++i) {
			if (holder_[i] == kChancePlayerId) {
				sum++;
			}
		}
		return sum == 0;
	}

	bool IsChanceNode() { return player_ == kChancePlayerId; }

	int CurrentPlayer() { return player_; }
	
	std::vector<std::pair<Action, double>> ChanceOutcomes() const {
		std::vector<std::pair<Action, double>> outcomes;
		return outcomes;
	}
	std::string ActionToString(Player player, Action move) const {
		return std::to_string(player) + " " + CardString(move,num_suits_) + "\n";
	}
	std::string ToString() {
		std::string out;
		for (int i = 0; i < history_.size(); ++i) {
			out += ActionToString(history_[i].player, history_[i].action);
		}
		return out;
	}
	std::vector<Action> LegalActions() {
		std::vector<Action> actions;
		if (IsTerminal()) return {};
		if (IsChanceNode()) {
			for (int i = 0; i < holder_.size(); ++i) {
				if (holder_[i] == kChancePlayerId) {
					actions.push_back(i);
				}
			}
		}
		else {
			//lead//
			if (history_.back().player == kChancePlayerId) {
				std::vector<Action> void_actions;
				for (int i = 0; i < holder_.size(); ++i) {
					if (holder_[i] == player_) {
						actions.push_back(i);
					}
				}
			}
			//follow//
			else {
				std::vector<Action> void_actions;
				for (int i = 0; i < holder_.size(); ++i) {
					if (holder_[i] == player_) {
						if (CardSuit(history_.back().action, num_suits_) == CardSuit(i, num_suits_)) {
							actions.push_back(i);
						}
						else {
							void_actions.push_back(i);
						}
					}
				}
				if (actions.size() == 0) {
					actions = void_actions;
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
			holder_[move]=moves_%2;
		}
		else if (moves_ == (kNumSuits * kNumRanks / 2)) {
			trump_ = CardSuit(move, num_suits_);
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
				lead_win = Trick(history_[moves_ - 3].action, history_[moves_ -2].action);
				winner = (lead_win) ^ (history_[moves_- 3].player == 0) ? 1 : 0;
				player_ = winner;
				break;
			case 1:
				//establishing lead//
				holder_[move] = 2;
				(player_ == 0) ? player_ = 1 : player_ = 0;
				break;
			case 2:
				//following and awarding face up//
				holder_[move] = 2;
				lead_win = Trick(history_[moves_ - 1].action, move);
				winner = (lead_win) ^ (history_[moves_ - 1].player == 0) ? 1 : 0;
				holder_[history_[moves_ - 2].action]=winner;
				player_ = kChancePlayerId;
				break;
			case 3:
				//awarding face down//
				lead_win = Trick(history_[moves_ - 2].action, history_[moves_ - 1].action);
				loser = (lead_win) ^ (history_[moves_ - 1].player == 0) ? 0 : 1;
				holder_[move]=loser;
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
	std::vector<double> Returns() {
		return std::vector<double>(2, 0);
	}
};
