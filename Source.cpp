#include <vector>
#include <algorithm>
#include <unordered_map>
#include <intrin.h>
#include <array>
#include <iostream>
#include <chrono>
#include <cassert>
#include <random>
//#define DEBUG
const int kNumSuits = 4;
const int kNumRanks = 13;
struct Pair {
	char index;
	char value;
	Pair(char index_, char value_) {
		index = index_;
		value = value_;
	}
	bool operator<(Pair &pair) {
		return value < pair.value;
	}
};
struct Action {
	uint32_t index;
	unsigned char suit;
	bool player;
	Action(uint32_t index_, unsigned char suit_, bool player_) {
		index = index_;
		suit = suit_;
		player = player_;
	}
};
struct ActionValue {
	Action action;
	int value;
	bool operator<(ActionValue& aval) {
		return value < aval.value;
	}
};

class Node {
private:
	uint32_t cards_;
	std::array<uint32_t, kNumSuits> suit_masks_;
	unsigned char trump_;
	char score_;
	unsigned char moves_;
	bool player_;
	std::vector<Action> history_;
	uint64_t key_;
public:
	Node(uint32_t cards, std::array<uint32_t, kNumSuits> suit_masks, char trump) {
		cards_ = cards;
		suit_masks_ = suit_masks;
		trump_ = trump;
		moves_ = 0;
		player_ = 0;
		score_ = 0;
		history_ = {};
	};
	bool Player() { return player_; };
	char Score() { return score_; };
	char Moves() { return moves_; };
	bool IsTerminal() {
		return (moves_ == 2 * kNumRanks);
	}
	char RemainingTricks() {
		return (int)(kNumRanks-(moves_>>1));
	}
	uint32_t Cards() { return cards_; }
	std::array<uint32_t, kNumSuits> SuitMasks() { return suit_masks_; }
	uint64_t GetNodeKey() { return key_; }
	bool Trick(Action lead, Action follow) {
		//true if leader won//
		return (lead.suit != follow.suit && lead.suit == trump_) || (lead.suit == follow.suit && lead.index <= follow.index);
	}
	int LeadOrdering(Action action) {
		ApplyAction(action);
		std::vector<Action> moves = MoveGen();
		UndoAction(action);
		int sum = 0;
		for (size_t i = 0; i < moves.size(); ++i) {
			sum += Trick(action, moves[i]);
		}
		if (sum == moves.size()) {
			return action.suit==trump_?0:-1;//intriguing this seems to produce small perfomance increase//
		}
		if (sum == 0) {
			return 2;
		}
		else {
			return 1;
		}
	}
	 uint32_t QuickTricks() {
		//returns a simple lower bound for the leader on the tricks they can win and a lower bound for the follower//
		//lower bound for leader is how many tricks they can win without losing lead//
		//follow is how many tricks they can win regardless of lead//
		std::array<uint32_t, kNumSuits> lead_suit_lengths;
		std::array<uint32_t, kNumSuits> follow_suit_lengths;
		bool lead = player_;
		bool follow = !player_;
		uint32_t quick=0;
		std::array<uint32_t, kNumSuits> lead_winners = {0,0,0,0};
		std::array<uint32_t, kNumSuits> follow_winners = { 0,0,0,0};
		for(size_t i = 0; i < kNumSuits; ++i) {
			uint32_t lead_cards=_bzhi_u32(~0,RemainingTricks()*2);
			uint32_t follow_cards= _bzhi_u32(~0, RemainingTricks() * 2);
			lead == 0 ? lead_cards = lead_cards&(~cards_),follow_cards=follow_cards&cards_:follow_cards = follow_cards&(~cards_),lead_cards=lead_cards&cards_ ;
			lead_suit_lengths[i] = __popcnt(lead_cards & suit_masks_[i]);
			follow_suit_lengths[i]= __popcnt(follow_cards & suit_masks_[i]);
			lead_cards = _bzhi_u32(~0, RemainingTricks() * 2);
			follow_cards = _bzhi_u32(~0, RemainingTricks() * 2);
			lead == 0 ? lead_cards = lead_cards & (cards_), follow_cards = follow_cards & (~cards_) : follow_cards = follow_cards & (cards_), lead_cards = lead_cards & (~cards_);
			if (lead_suit_lengths[i] != 0) {
				lead_winners[i] += _tzcnt_u32(lead_cards & suit_masks_[i]) - _tzcnt_u32(suit_masks_[i]);
			}
			if (follow_suit_lengths[i]!= 0) {
				follow_winners[i]+= _tzcnt_u32(follow_cards & suit_masks_[i]) - _tzcnt_u32(suit_masks_[i]);
			}
		}
		for (size_t i = 0; i < kNumSuits; ++i) {  
		#ifdef DEBUG
			std::cout << "Lead is " << lead << " with " <<lead_winners[i]<< " winners in suit "<<i<< std::endl;
			std::cout << "Follow is " << follow << " with " <<follow_winners[i]<< " winners in suit "<<i << std::endl;
			std::cout << " Lead has " << lead_suit_lengths[i] << " in suit " << i << std::endl;
			std::cout << " Follow has " << follow_suit_lengths[i] << " in suit " << i << std::endl;
		#endif
			
			if (follow_suit_lengths[trump_] == 0) {
				quick += lead_winners[i];
			}
			else {
				quick += std::min(lead_winners[i], follow_suit_lengths[i]);
			}
		}
		return quick;
	}
	void RemoveCard(Action action) {
		//Removes card from cards_//
		uint32_t mask_b = ~0;
		mask_b =_bzhi_u32(mask_b, action.index);
		uint32_t mask_a = ~mask_b;
		mask_a = _blsr_u32(mask_a);
		uint32_t copy_a = cards_ & mask_a;
		uint32_t copy_b = cards_ & mask_b;
		copy_a = copy_a >> 1;
		cards_ = copy_a | copy_b;
		//decrements appropriate suits//
		suit_masks_[action.suit] = _blsr_u32(suit_masks_[action.suit])>>1;
		char suit = action.suit;
		suit++;
		while (suit < kNumSuits) {
			suit_masks_[suit]=suit_masks_[suit] >> 1;
			suit++;
		}
	}
	void InsertCard(Action action) {
		//inserts card into cards_//
		uint32_t mask_b = ~0;
		mask_b = _bzhi_u32(mask_b, action.index);
		uint32_t mask_a = ~mask_b;
		uint32_t copy_b = cards_ & mask_b;
		uint32_t copy_a = cards_ & mask_a;
		copy_a = copy_a << 1;
		uint32_t card = action.player<< action.index;
		cards_ = card | copy_a | copy_b;
		//increments appropriate suits//
		uint32_t new_suit = (suit_masks_[action.suit] & mask_b )| (1 << action.index);
		suit_masks_[action.suit] = ((suit_masks_[action.suit] & mask_a) << 1 )| new_suit;
		char suit = action.suit;
		suit++;
		while (suit < kNumSuits) {
			suit_masks_[suit] = suit_masks_[suit] << 1;
			suit++;
		}
	}
	void UpdateNodeKey() {
		//recasts the cards and suitlengths into canonical form//
		//least sig part of 32bit card is trump, then suits in ascending length//
		uint64_t suit_sig = 0;
		char trump_length = __popcnt(suit_masks_[trump_]);
		std::vector<Pair> non_trump_lengths;
		for (size_t i = 0; i < kNumSuits; ++i) {
			if (i != trump_) {
				non_trump_lengths.push_back(Pair(i, __popcnt(suit_masks_[i])));
			}
		}
		std::sort(non_trump_lengths.begin(), non_trump_lengths.end());
		suit_sig = suit_sig | trump_length;
		for (size_t i = 0; i < non_trump_lengths.size(); ++i) {
			suit_sig = suit_sig | ((uint64_t)non_trump_lengths[i].value << (4*(i+1)));
		}
		suit_sig = suit_sig << 32;
		std::array<uint32_t, kNumSuits> suit_cards;
		suit_cards[0] = cards_ & suit_masks_[trump_];
		if (suit_masks_[trump_] != 0) {
			suit_cards[0] = suit_cards[0] >> _tzcnt_u32(suit_masks_[trump_]);
		}
		uint32_t sum = __popcnt(suit_masks_[trump_]);
		uint32_t cards = 0|suit_cards[0];
		for (size_t i = 0; i < non_trump_lengths.size(); ++i) {
			suit_cards[i] = cards_ & suit_masks_[non_trump_lengths[i].index];
			uint32_t val = 0;
			if (suit_masks_[non_trump_lengths[i].index] != 0) {
				val = _tzcnt_u32(suit_masks_[non_trump_lengths[i].index]);
			}
			suit_cards[i]= suit_cards[i] >>val;
			suit_cards[i] = suit_cards[i] << sum;
			sum += __popcnt(suit_masks_[non_trump_lengths[i].index]);
			cards = cards | suit_cards[i];
		}
		cards = cards | (player_ << 31);
		key_ = suit_sig | (uint64_t)cards;
	#ifdef DEBUG_KEY
		std::cout <<"CARDS_ " << cards_ << std::endl;
		std::cout << "CARDS " << cards << std::endl;
		std::cout << "SUIT MASKS " << std::endl;
		for (int i = 0; i < kNumSuits; ++i) {  
			std::cout << suit_masks_[i] << std::endl;
		}
		std::cout << "SUIT_SIG " << suit_sig << std::endl;
		std::cout<<"KEY " << key_ << std::endl;
	#endif 
	}
	std::vector<Action> MoveGen() {
		//Features//
		//strategically equivalent move fusion//
		//move ordering on follow except trying out trumps first//
		//move ordering on lead going win by force first,uncertain,guaranteed losers//
		std::vector<Action> out = {};
		uint32_t copy_cards = cards_;
		std::array<uint32_t, kNumSuits> player_suit_masks;
		if (player_ == 0) {
			copy_cards = ~copy_cards;
		}
		for (size_t i = 0; i < kNumSuits; ++i) {
			uint32_t suit_cards = copy_cards & suit_masks_[i];
			player_suit_masks[i] = suit_cards&~(suit_cards>>1);
			#ifdef DEBUG
			std::cout << "Cards " << cards_ << std::endl;
			std::cout << "Suit Mask " << i << " " << suit_masks_[i] << std::endl;
			std::cout << "Player " << player_ << " suit mask " << (int)i << " " << player_suit_masks[i] << std::endl;
			#endif
		}
		if (moves_%2==0) {
			std::vector<ActionValue> temp = {};
			for (size_t i = 0; i < kNumSuits; ++i) {
				uint32_t j = 0;
				while (player_suit_masks[i] != 0) {
					uint32_t best = _tzcnt_u32(player_suit_masks[i]);
					j += best;
					temp.push_back({ Action(j, i, player_),LeadOrdering(Action(j, i, player_)) });
					player_suit_masks[i]=player_suit_masks[i] >> best+1;
					j++;
				}
			}
			std::sort(temp.begin(), temp.end());
			for (size_t i = 0; i < temp.size(); ++i) {
				out.push_back(temp[i].action);
			}
		}
		else {
			char suit = history_.back().suit;
			if (player_suit_masks[suit] != 0) {
				uint32_t worst = 31 - _lzcnt_u32(player_suit_masks[suit]);
				uint32_t mask = _bzhi_u32(~0,history_.back().index);
				uint32_t sup_mask = player_suit_masks[suit] & mask;   
				if (sup_mask != 0) {
					uint32_t sup = 31 - _lzcnt_u32(sup_mask);
					if (sup != worst) {
						out.push_back(Action(sup, suit, player_));
					}
				}
				out.push_back(Action(worst,suit,player_));
			}
			else {
				for (size_t i = 0; i < kNumSuits; ++i) {
					if (i != suit&&player_suit_masks[i]!=0) {
						uint32_t worst = 31 - _lzcnt_u32(player_suit_masks[i]);
						out.push_back(Action(worst, i, player_));
					}
				}
			}
		}
		#ifdef DEBUG
			std::cout << "Player " << player_ <<" MoveGen " << std::endl;
			for (size_t i = 0; i < out.size(); ++i) {
				std::cout << out[i].index << " " << (int)out[i].suit << std::endl;
			}  
		#endif

		return out;

	}
	void ApplyAction(Action action) {
		#ifdef DEBUG
			std::cout << "Player " << player_ << " ApplyAction " << action.index << " " << (int)action.suit << std::endl;
		#endif
		if (moves_ % 2 == 1) {
			Action lead = history_[history_.size() - 1];
			bool winner = !((Trick(lead, action)) ^ lead.player);
		#ifdef DEBUG
			std::cout << "Player " << winner << " won this trick" << std::endl;
		#endif
			score_ += (winner == 0);
			player_ = (winner);
		}
		else {
			player_ = !player_;
		}
		#ifdef DEBUG
			assert((suit_masks_[0] & suit_masks_[1]) == 0);
			assert((suit_masks_[0] & suit_masks_[2])== 0);
			assert((suit_masks_[0] & suit_masks_[3]) == 0);
			assert((suit_masks_[1] & suit_masks_[2]) == 0);
			assert((suit_masks_[1] & suit_masks_[3]) == 0);
			assert((suit_masks_[2] & suit_masks_[3]) == 0);
		#endif
		RemoveCard(action);
		moves_++;
		history_.push_back(action);
	}
	void UndoAction(Action action) {
		if (moves_ % 2 == 0) {
			Action lead = history_[history_.size() - 2];
			Action follow = history_[history_.size() - 1];
			bool winner = !(Trick(lead, follow) ^ lead.player);
			score_ -= (winner == 0);
		}
		InsertCard(action);
		moves_--;
		player_=history_.back().player;
		history_.pop_back();
		#ifdef DEBUG
			std::cout << "Player " << player_ << " UndoAction " << action.index << " " << (int)action.suit << std::endl;
		#endif
	}
};



//solvers below
int AlphaBeta(Node* node, int alpha, int beta, int& counter) {
	//counter tracks number of calls to search//
	//fail soft ab search
	counter++;
	if (node->IsTerminal()) {
		return node->Score();
	}
	else if (node->Player() == 0) {
		int val = 0;
		std::vector<Action> actions = node->MoveGen();
		for (int i = 0; i < actions.size(); ++i) {
			node->ApplyAction(actions[i]);
			val = std::max(val, AlphaBeta(node, alpha, beta, counter));
			node->UndoAction(actions[i]);
			alpha = std::max(val, alpha);
			if (val >= beta) {
				break;
			}
		}
		return val;
	}
	else if (node->Player() == 1) {
		int val =kNumRanks;
		std::vector<Action> actions = node->MoveGen();
		for (int i = 0; i < actions.size(); ++i) {
			node->ApplyAction(actions[i]);
			val = std::min(val, AlphaBeta(node, alpha, beta, counter));
			node->UndoAction(actions[i]);
			beta = std::min(val, beta);
			if (val <= alpha) {
				break;
			}
		}
		return val;
	}
};

struct Bounds {
	char lower;
	char upper;
};

char AlphaBetaMemory(Node* node, char alpha, char beta, int& counter, std::unordered_map<uint64_t, Bounds>* TTable) {
	//counter tracks number of calls to search//
	//fail soft ab search
	counter++;
	char val = 0;
	uint64_t key = 0;
	if (node->IsTerminal()) {
		return node->Score();
	}
	if(node->Moves()%2==0){
		node->UpdateNodeKey();
		key = node->GetNodeKey();
		if (TTable->find(key) == TTable->end()) {
			//uint32_t quick = node->QuickTricks();
			//if (node->Player() == 0) {
				//TTable->insert({ key,{(int)quick,(int)(node->RemainingTricks())} });
			//}
			//else {
				//TTable->insert({ key,{0,(int)(node->RemainingTricks() - quick)} });
			//}
			TTable->insert({ key,{0,node->RemainingTricks()} });
		}
		char lower = TTable->at(key).lower;
		char upper = TTable->at(key).upper;
		if (lower == upper) {
			return node->Score() +lower;
		}
		if (lower + node->Score() >= beta) {
			return lower + node->Score();
		}
		if (upper + node->Score() <= alpha) {
			return upper + node->Score();
		}
		alpha = std::max(alpha,(char)(lower + node->Score()));
		beta = std::min(beta,(char)(upper + node->Score()));
	}
	
	if (node->Player() == 0) {
		val = node->Score();
		char a = alpha;
		std::vector<Action> actions = node->MoveGen();
		for (int i = 0; i < actions.size(); ++i) {
			node->ApplyAction(actions[i]);
			val = std::max(val, AlphaBetaMemory(node, a, beta, counter, TTable));
			node->UndoAction(actions[i]);
			a = std::max(val, a);
			if (val >= beta) {
				break;
			}
		}
	}
	else if (node->Player() == 1) {
		val = node->RemainingTricks()+node->Score();
		char b = beta;
		std::vector<Action> actions = node->MoveGen();
		for (int i = 0; i < actions.size(); ++i) {
			node->ApplyAction(actions[i]);
			val = std::min(val, AlphaBetaMemory(node, alpha, b, counter, TTable));
			node->UndoAction(actions[i]);
			b = std::min(val, b);
			if (val <= alpha) {
				break;
			}
		}
	}
	if (val <= alpha && node->Moves() % 2 == 0) {
		TTable->at(key).upper = val - node->Score();
	}
	if (val > alpha && val < beta && node->Moves() % 2 == 0) {
		TTable->at(key).upper = val - node->Score();
		TTable->at(key).lower = val - node->Score();
	}
	if (val >= beta && node->Moves() % 2 == 0) {
		TTable->at(key).lower = val - node->Score();
	}
	return val;
};

char MTD(Node* node,char guess, int& counter, std::unordered_map<uint64_t,Bounds>* TTable) {
	char g = guess;
	char upperbound = 13;
	char lowerbound = 0;
	while (lowerbound < upperbound) {
		char alpha;
		char beta;
		(g == lowerbound) ? beta = g + 1 : beta = g;
		g = AlphaBetaMemory(node, beta - 1, beta, counter, TTable);
		(g < beta) ? upperbound = g : lowerbound = g;
	}
	return g;
}



 std::vector<Node> GWhistGenerator(int num,unsigned long long seed){
	 std::vector<Node> out = {};
	 std::mt19937 g(seed);
	 std::array<int, 2 * kNumRanks> nums;
	 for (int i = 0; i < 2 * kNumRanks; ++i) {
		 nums[i] = i;
	 }
	 for (int i = 0; i < num; ++i) {
		 std::shuffle(nums.begin(), nums.end(), g);
		 uint32_t cards = 0;
		 std::array<uint32_t, kNumSuits> suits;
		 for (int j = 0; j < kNumRanks; ++j) {
			 cards = cards | (1 << nums[j]);
		 }
		 std::shuffle(nums.begin(), nums.end(), g);
		 std::array<int, kNumSuits> temp;
		 for (int j = 0; j < kNumSuits-1; ++j) {
			 temp[j] = nums[j];
		 }
		 temp[kNumSuits - 1] = 2 * kNumRanks;
		 std::sort(temp.begin(), temp.end());
		 for (int j = 0; j < kNumSuits; ++j) {
			 if (j == 0) {
				 suits[j] = _bzhi_u32(~0, temp[j]);
			 }
			 else {
				 suits[j] = (_bzhi_u32(~0, temp[j])) ^ _bzhi_u32(~0, temp[j-1]);
				 //assert((suits[j] & suits[j - 1])== 0);
			 }
		 }
		 out.push_back(Node(cards, suits, 0));
		#ifdef DEBUG
		 std::cout << __popcnt(cards) << " " << __popcnt(suits[0]) + __popcnt(suits[1]) + __popcnt(suits[2]) + __popcnt(suits[3]) << std::endl;
		 std::cout << cards << " " << suits[0] << " " << suits[1] << " " << suits[2] << " " << suits[3] << std::endl;
		#endif

	 }
	 return out;
 }
 //DONE //
 //MOVE ORDERING, STRATEGIC MOVE FUSION, ALPHA BETA PRUNING, TRANSPOSITION TABLE, RANDOM ENDGAME GENERATION//
 // CORRECT ALPHABETAMEMORY SEARCH IMPLEMENTED,
 //
 //TO IMPLEMENT/ ISSUES //
 //QUICKLATE TRICKS PRODUCES UNSOUND SEARCH : IMPLEMENT A FUNCTIONING VERSION (HAGLUND) AND SEE IF IT IMPROVES PERFORMANCE//
 //IMPLEMENT LRU CACHE TO PREVENT CONTAINER OVERFLOW//
 //FORMAL TESTS?//
int main() {
	uint32_t cards = 0b10101010110100100011111000;
	std::array<uint32_t, kNumSuits> suits = { 0b111111,0b1111111000000,0b1111110000000000000,0b11111110000000000000000000};
	Node test_node0(cards, suits, 0);
	Node test_node1(cards, suits, 1);
	Node test_node2(cards, suits, 2);
	Node test_node3(cards, suits, 3);
	int counter = 0;
	std::vector<Node> nodes = GWhistGenerator(100000, 1);
	std::unordered_map<uint64_t, int> TTable0 = {};
	std::unordered_map<uint64_t,Bounds> TTable1 = {};
	std::unordered_map<uint64_t, char> TTable2 = {};
	std::cout << TTable1.max_size() << std::endl;
	std::cout << TTable2.max_size() << std::endl;
	std::vector<int> results = {};
	const auto start{ std::chrono::steady_clock::now() };
	//int var1 = MTD(&test_node0, 0, counter, &TTable1);
	int inconsistentc = 0;
	int inconsistentm = 0;
	for (auto it = nodes.begin(); it != nodes.end(); ++it) {
		//int abc = AlphaBetaCache(&*it, 0, 13, counter, &TTable0);
		char abm =MTD(&*it,0,counter, &TTable1);
		//results.push_back(abm);
		//int ab = AlphaBeta(&*it, 0, 13, counter);
		//if (abc!=ab) {
			//std::cout << "Inconsistency across search paradigms" << std::endl;
			//inconsistentc++;
		//}
		//if (abm != ab) {
			//inconsistentm++;
		//}
	}
	const auto end{ std::chrono::steady_clock::now() };
	const std::chrono::duration<double> elapsed_seconds{ end - start };
	std::cout << elapsed_seconds.count() << std::endl;
	std::cout << counter << std::endl;
	std::cout << inconsistentc << std::endl;
	std::cout << inconsistentm << std::endl;
	//std::cout << results[0] << std::endl;
	//std::cout << results[50000] << std::endl;
	//std::cout << results[99999] << std::endl;
	//std::cout << var1 << std::endl;
	//std::cout << var2 << std::endl;
	//std::cout << var3 << std::endl;
	
}
  