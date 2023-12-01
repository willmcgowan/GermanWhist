//
//  main.cpp
//  GermanWhist
//
#include <vector>
#include <algorithm>
#include <unordered_map>
#include <x86intrin.h>
#include <array>
#include <iostream>
#include <chrono>
#include <cassert>
#include <random>
#include <ratio>
#include <fstream>
#include <string>
//#include <omp.h>
  
//#define DEBUG
const int kNumSuits = 4;
const int kNumRanks = 13;
struct Triple {
    char index;
    char length;
    uint32_t sig;
    bool operator<(const Triple& triple) const {
        return (length < triple.length)|| (length == triple.length && sig < triple.sig);
    }
};

struct Pair {
    char index;
    char value;
    Pair(char index_, char value_) {
        index = index_;
        value = value_;
    }
    bool operator<(const Pair &pair) const {
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
    bool operator<(const ActionValue& aval) const {
        return value < aval.value;
    }
};

class Node {
private:
    uint32_t cards_;
    std::array<uint32_t, kNumSuits> suit_masks_;
    char total_tricks_;
    char trump_;
    char score_;
    char moves_;
    bool player_;
    std::vector<Action> history_;
    uint64_t key_;
public:
    Node(uint32_t cards, std::array<uint32_t, kNumSuits> suit_masks, char trump,bool player) {
        cards_ = cards;
        suit_masks_ = suit_masks;
        total_tricks_ = __builtin_popcount(cards);
        trump_ = trump;
        moves_ = 0;
        player_ = player;
        score_ = 0;
        history_ = {};
    };
    bool Player() { return player_; };
    char Score() { return score_; };
    char Moves() { return moves_; };
    bool IsTerminal() {
        return (moves_ == 2 * total_tricks_);
    }
    char RemainingTricks() {
        return (char)(total_tricks_-(moves_>>1));
    }
    char TotalTricks() {
        return total_tricks_;
    }
    uint32_t Cards() { return cards_; }
    std::array<uint32_t, kNumSuits> SuitMasks() { return suit_masks_; }
    uint64_t GetNodeKey() { return key_; }
    bool Trick(Action lead, Action follow) {
        //true if leader won//
        return (lead.suit != follow.suit && lead.suit == trump_) || (lead.suit == follow.suit && lead.index <= follow.index);
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
        //recasts the cards and suitlengths into quasi-canonical form//
        //least sig part of 32bit card is trump, then suits in ascending length//
        
        //note this canonical form does not take advantage of all isomorphisms//
        //suppose a game is transformed as follows: all card bits flipped and the player bit flipped, ie player 1 has the lead and has player 0s cards from the original game//
        //this implies player 1 achieves the minimax value of the original game ie the value is remaining tricks - value of the original game for this transformed game//
        //also does not take advantage of single suit isomorphism. Namely all single suit games with the same card distribution are isomorphic. Currently this considers all trump, all no trump games as distinct//
        uint64_t suit_sig = 0;
        char trump_length = __builtin_popcount(suit_masks_[trump_]);
        if (trump_length > kNumRanks) {
            throw;
        }
        std::vector<Triple> non_trump_lengths;
        for (char i = 0; i < kNumSuits; ++i) {
            if (i != trump_) {
                char length = __builtin_popcount(suit_masks_[i]);
                uint32_t sig = suit_masks_[i]&cards_;
                if (suit_masks_[i] != 0) {
                    sig = (sig >> (_tzcnt_u32(suit_masks_[i])));
                }
                if (length > kNumRanks) {
                    throw 1;
                }
                non_trump_lengths.push_back(Triple{i,length,sig });
            }
        }
        //sorting takes advantage of two isomorphisms namely nontrump suits of nonequal length can be exchanged and the value of the game does not change//
        //and this more complicated suppose two games with two or more (non_trump)suits of equal length, permuting those suits should not change the value of solved game ie it is an isomorphism//
        std::sort(non_trump_lengths.begin(), non_trump_lengths.end());
        suit_sig = suit_sig | trump_length;
        for (size_t i = 0; i < non_trump_lengths.size(); ++i) {
            suit_sig = suit_sig | ((uint64_t)non_trump_lengths[i].length << (4*(i+1)));
        }
        suit_sig = suit_sig << 32;
        std::array<uint32_t, kNumSuits> suit_cards;
        suit_cards[0] = cards_ & suit_masks_[trump_];
        if (suit_masks_[trump_] != 0) {
            suit_cards[0] = suit_cards[0] >> _tzcnt_u32(suit_masks_[trump_]);
        }
        uint32_t sum = __builtin_popcount(suit_masks_[trump_]);
        uint32_t cards = 0|suit_cards[0];
        for (size_t i = 0; i < non_trump_lengths.size(); ++i) {
            suit_cards[i] = cards_ & suit_masks_[non_trump_lengths[i].index];
            uint32_t val = 0;
            if (suit_masks_[non_trump_lengths[i].index] != 0) {
                val = _tzcnt_u32(suit_masks_[non_trump_lengths[i].index]);
            }
            suit_cards[i]= suit_cards[i] >>val;
            suit_cards[i] = suit_cards[i] << sum;
            sum += __builtin_popcount(suit_masks_[non_trump_lengths[i].index]);
            cards = cards | suit_cards[i];
        }
        //cards = cards | (player_ << 31);
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
    uint64_t AltKey() {
        uint32_t mask = _bzhi_u32(~0, 2 * RemainingTricks());
        return key_ ^ (uint64_t)mask;
    }
    //Move Ordering Heuristics//
    //These could Definitely be improved, very hacky//
    int LeadOrdering(Action action) {
        char suit = action.suit;
        uint32_t copy_cards = cards_;
        if (player_ == 0) {
            copy_cards = ~copy_cards;
        }
        uint32_t suit_cards = copy_cards & suit_masks_[suit];
        uint32_t mask = suit_cards & ~(suit_cards >> 1);
        //represents out of the stategically inequivalent cards in a suit that a player holds, what rank is it, rank 0 is highest rank etc//
        int suit_rank = __builtin_popcount(_bzhi_u32(mask, action.index));
        ApplyAction(action);
        std::vector<Action> moves = LegalActions();
        UndoAction(action);
        int sum = 0;
        for (size_t i = 0; i < moves.size(); ++i) {
            sum += Trick(action, moves[i]);
        }
        if (sum == moves.size()) {
            return action.suit == trump_ ? 0 - suit_rank : -1 * kNumRanks - suit_rank;//intriguing this seems to produce small perfomance increase//
        }
        if (sum == 0) {
            return 2 * kNumRanks - suit_rank;
        }
        else {
            return 1 * kNumRanks - suit_rank;
        }
    }
    int FollowOrdering(Action action) {
        Action lead = history_.back();
        //follow ordering for fast cut offs//
        //win as cheaply as possible, followed by lose as cheaply as possible
        char suit = action.suit;
        uint32_t copy_cards = cards_;
        if (player_ == 0) {
            copy_cards = ~copy_cards;
        }
        uint32_t suit_cards = copy_cards & suit_masks_[suit];
        uint32_t mask = suit_cards & ~(suit_cards >> 1);
        //represents out of the stategically inequivalent cards in a suit that a player holds, what rank is it, rank 0 is highest rank etc//
        int suit_rank = __builtin_popcount(_bzhi_u32(mask, action.index));
        if (!Trick(lead, action)) {
            return -kNumRanks - suit_rank;
        }
        else {
            return -suit_rank;
        }
    }
    
    

    std::vector<Action> LegalActions() {
        //Features//
        //Move fusion and move ordering//
        std::vector<Action> out;
        out.reserve(kNumRanks);
        uint32_t copy_cards = cards_;
        std::array<uint32_t, kNumSuits> player_suit_masks;
        if (player_ == 0) {
            copy_cards = ~copy_cards;
        }
        for (size_t i = 0; i < kNumSuits; ++i) {
            uint32_t suit_cards = copy_cards & suit_masks_[i];
            player_suit_masks[i] = suit_cards & ~(suit_cards >> 1);
#ifdef DEBUG
            std::cout << "Cards " << cards_ << std::endl;
            std::cout << "Suit Mask " << i << " " << suit_masks_[i] << std::endl;
            std::cout << "Player " << player_ << " suit mask " << (int)i << " " << player_suit_masks[i] << std::endl;
#endif
        }
        std::vector<ActionValue> temp;
        temp.reserve(kNumRanks);
        for (char i = 0; i < kNumSuits; ++i) {
            uint32_t suit_mask = player_suit_masks[i];
            bool lead = (moves_ % 2 == 0);
            bool follow = (moves_ % 2 == 1);
            bool correct_suit = 0;
            bool void_in_suit = 0;
            if (follow == true) {
                correct_suit = (history_.back().suit == i);
                void_in_suit = (player_suit_masks[history_.back().suit] == 0);
            }
            if ((lead || (follow && (correct_suit || void_in_suit)))) {
                while (suit_mask != 0) {
                    uint32_t best = _tzcnt_u32(suit_mask);
                    if (moves_ % 2 == 0) {
                        temp.push_back({ Action(best, i, player_),LeadOrdering(Action(best, i, player_)) });
                    }
                    else {
                        temp.push_back({ Action(best, i, player_),FollowOrdering(Action(best, i, player_)) });
                    }
                    suit_mask = _blsr_u32(suit_mask);
                }
            }
        }
        std::sort(temp.begin(), temp.end());
        for (size_t i = 0; i < temp.size(); ++i) {
            out.push_back(temp[i].action);
        }
        
#ifdef DEBUG
        std::cout << "Player " << player_ << " MoveGen " << std::endl;
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
            Action lead = history_.back();
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
int AlphaBeta(Node* node, int alpha, int beta) {
    //fail soft ab search
    if (node->IsTerminal()) {
        return node->Score();
    }
    else if (node->Player() == 0) {
        int val = 0;
        std::vector<Action> actions = node->LegalActions();
        for (int i = 0; i < actions.size(); ++i) {
            node->ApplyAction(actions[i]);
            val = std::max(val, AlphaBeta(node, alpha, beta));
            node->UndoAction(actions[i]);
            alpha = std::max(val, alpha);
            if (val >= beta) {
                break;
            }
        }
        return val;
    }
    else if (node->Player() == 1) {
        int val =node->TotalTricks();
        std::vector<Action> actions = node->LegalActions();
        for (int i = 0; i < actions.size(); ++i) {
            node->ApplyAction(actions[i]);
            val = std::min(val, AlphaBeta(node, alpha, beta));
            node->UndoAction(actions[i]);
            beta = std::min(val, beta);
            if (val <= alpha) {
                break;
            }
        }
        return val;
    }
    return -1;
};



//Helper Functions//
std::vector<uint32_t> GenQuads(int size_endgames) {
    //Generates Suit splittings for endgames of a certain size//
    std::vector<uint32_t> v;
    for (char i = 0; i <= std::min(size_endgames * 2, kNumRanks); ++i) {
        int sum = size_endgames * 2 - i;
        for (char j = 0; j <= std::min(sum, kNumRanks); ++j) {
            for (char k = std::max((int)j, sum - j - kNumRanks); k <= std::min(sum - j, kNumRanks); ++k) {
                char l = sum - j - k;
                if (l < k) {
                    break;
                }
                else {
                    uint32_t num = 0;
                    num = num | (i);
                    num = num | (j << 4);
                    num = num | (k << 8);
                    num = num | (l << 12);
                    v.push_back(num);
                }
            }
        }
    }
    return v;
}
std::vector<std::vector<uint32_t>> BinCoeffs(uint32_t max_n) {
    //tabulates binomial coefficients//
    std::vector<std::vector<uint32_t>> C(max_n+1,std::vector<uint32_t>(max_n+1));
    for (uint32_t i = 1; i <= max_n; ++i) {
        C[0][i] = 0;
    }
    for (uint32_t i = 0; i <= max_n; ++i) {
        C[i][0] = 1;
    }
    for (uint32_t i = 1; i <= max_n; ++i) {
        for (uint32_t j = 1; j <= max_n; ++j) {
            C[i][j] = C[i - 1][j] + C[i - 1][j - 1];
        }
    }
    return C;
}
//Credit to computationalcombinatorics.wordpress.com
uint32_t HalfUnColexer(uint32_t k,uint32_t m,std::vector<std::vector<uint32_t>> bin_coeffs) {
    //generates cards_ from colexicographical index//
    std::vector<int> S(k,0);
    for(int i =0;i<k;++i){
        S[i]=i;
    }
    int i = k-1;
    while(i>=0){
        int l =i;
        while(bin_coeffs[l][i+1]<=m){
            l++;
        }
        S[i]=l-1;
        m=m-bin_coeffs[l-1][i+1];
        i--;
    }
    uint32_t out = 0;
    for(int i =0;i<S.size();++i){
        out = out|(1<<S[i]);
    }
    return out;
}
uint32_t HalfColexer(uint32_t cards,std::vector<std::vector<uint32_t>>& bin_coeffs) {
    //returns the colexicographical ranking of a combination of indices where the the size of the combination is half that of the set of indices//
    uint32_t out = 0;
    uint32_t count = 0;
    while (cards != 0) {
        uint32_t ind = _tzcnt_u32(cards);
        uint32_t val = bin_coeffs[ind][count+1];
        out += val;
        cards = _blsr_u32(cards);
        count++;
    }
    return out;
}
//hideous code for generating the next colexicographical combination//
bool NextColex(std::vector<int>& v,int k){
    int num=0;
    for(int i=0;i<v.size();++i){
        if(v[i+1]-v[i]>1&&v[i+1]!=i){
            v[i]=v[i]+1;
            if(v[i]>k-v.size()+i){
                return false;
            }
            num = i;
            break;
        }
        if(i==v.size()-1){
            v[i]=v[i]+1;
            if(v[i]>k-v.size()+i){
                return false;
            }
            num=i;
            break;
        }
    }
    for(int i =0;i<num;++i){
        v[i]=i;
    }
    return true;
}

void GenSuitRankingsRel(uint32_t size, std::unordered_map<uint32_t, uint32_t>* Ranks) {
    //Generates ranking Table for suit splittings for endgames of a certain size//
    std::vector<uint32_t> v=GenQuads(size);
    for (uint32_t i = 0; i < v.size(); ++i) {
        //std::cout << "GenSuitRanks " << v[i] << "  " << i << std::endl;
        Ranks->insert({ v[i],i });
    }
}

void GenSuitRankingsAbs(uint32_t suit_split,std::unordered_map<uint32_t,uint32_t>* Ranks) {
    //Generates ranking table for all suit splittings//
    uint32_t counter;
    for (int i = 1; i <= kNumRanks; ++i) {
        std::vector<uint32_t> v = GenQuads(2 * i);
        for (int j = 0; j < v.size(); ++j) {
            Ranks->insert({ v[j],counter });
            counter++;
        }
    }
}

//used for retrosolving(minimal size container)//
//vector of chars but is really a wrapper for a vector of nybbles
class vectorNa {
private:
    std::vector<char> data;
public:
    vectorNa(size_t num, char val) {
        data = std::vector<char>((num >> 1)+1, val);
    }
    //OPERATOR OVERLOADS ACCESS RAW VECTOR OF CHARS//
    size_t size() const{
        return data.size();
    }
    char const& operator[](size_t index) const{
        return data[index];
    }
    void SetChar(size_t index, char value){
        data[index]=value;
    }
    char Get(size_t index){
        int remainder = index&0b1;
        if(remainder==0){
            return 0b1111&data[index>>1];
        }
        else{
            return ((0b11110000&data[index>>1])>>4);
        }
    }
    void Set(size_t index,char value){
        int remainder = index & 0b1;
        if (remainder == 0) {
            char datastore = 0b11110000 & data[index>>1];
            data[index>>1] = datastore|value;
        }
        else {
            char datastore = (0b1111 & data[index >> 1]);
            data[index >> 1] = datastore|(value << 4);
        }
    }
};
    
  
struct Bounds {
    char lower;
    char upper;
};
  
char AlphaBetaMemory(Node* node, char alpha, char beta, std::unordered_map<uint64_t, Bounds>* TTable) {
    //fail soft ab search
    char val = 0;
    uint64_t key = 0;
    if (node->IsTerminal()) {
        return node->Score();
    }
    if(node->Moves()%2==0){
        node->UpdateNodeKey();
        key = node->GetNodeKey();
        if (TTable->find(key) == TTable->end()) {
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
        std::vector<Action> actions;
        actions = node->LegalActions();
        for (int i = 0; i < actions.size(); ++i) {
            node->ApplyAction(actions[i]);
            val = std::max(val, AlphaBetaMemory(node, a, beta, TTable));
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
        std::vector<Action> actions;
        actions = node->LegalActions();
        for (int i = 0; i < actions.size(); ++i) {
            node->ApplyAction(actions[i]);
            val = std::min(val, AlphaBetaMemory(node, alpha, b, TTable));
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

char AlphaBetaMemoryIso(Node* node, char alpha, char beta, std::unordered_map<uint64_t, Bounds>* TTable) {
    //fail soft ab search
    char val = 0;
    uint64_t key = 0;
    bool player = node->Player();
    if (node->IsTerminal()) {
        return node->Score();
    }
    if (node->Moves() % 2 == 0) {
        node->UpdateNodeKey();
        key = (player) ?node->AltKey(): node->GetNodeKey();
        if (TTable->find(key) == TTable->end()) {
            TTable->insert({ key,{0,node->RemainingTricks()} });
        }
        char lower = (player)?node->RemainingTricks()-TTable->at(key).upper:TTable->at(key).lower;
        char upper = (player)? node->RemainingTricks() - TTable->at(key).lower :TTable->at(key).upper;
        if (lower == upper) {
            return node->Score() + lower;
        }
        if (lower + node->Score() >= beta) {
            return lower + node->Score();
        }
        if (upper + node->Score() <= alpha) {
            return upper + node->Score();
        }
        alpha = std::max(alpha, (char)(lower + node->Score()));
        beta = std::min(beta, (char)(upper + node->Score()));
    }

    if (node->Player() == 0) {
        val = node->Score();
        char a = alpha;
        std::vector<Action> actions;
        actions = node->LegalActions();
        for (int i = 0; i < actions.size(); ++i) {
            node->ApplyAction(actions[i]);
            val = std::max(val, AlphaBetaMemoryIso(node, a, beta, TTable));
            node->UndoAction(actions[i]);
            a = std::max(val, a);
            if (val >= beta) {
                break;
            }
        }
    }
    else if (node->Player() == 1) {
        val = node->RemainingTricks() + node->Score();
        char b = beta;
        std::vector<Action> actions;
        actions = node->LegalActions();
        for (int i = 0; i < actions.size(); ++i) {
            node->ApplyAction(actions[i]);
            val = std::min(val, AlphaBetaMemoryIso(node, alpha, b, TTable));
            node->UndoAction(actions[i]);
            b = std::min(val, b);
            if (val <= alpha) {
                break;
            }
        }
    }
    if (val <= alpha && node->Moves() % 2 == 0) {
        if (player) {
            TTable->at(key).lower = node->RemainingTricks() - (val - node->Score());
        }
        else {
            TTable->at(key).upper = val - node->Score();
        }
    }
    if (val > alpha && val < beta && node->Moves() % 2 == 0) {
        if (player) {
            TTable->at(key).lower = node->RemainingTricks() - (val - node->Score());
            TTable->at(key).upper = node->RemainingTricks() - (val - node->Score());
        }
        else {
            TTable->at(key).upper = val - node->Score();
            TTable->at(key).lower = val - node->Score();
        }
    }
    if (val >= beta && node->Moves() % 2 == 0) {
        if (player) {
            TTable->at(key).upper = node->RemainingTricks() - (val - node->Score());
        }
        else {
            TTable->at(key).lower = val - node->Score();
        }
    }
    return val;
};


char MTD(Node* node,char guess, std::unordered_map<uint64_t,Bounds>* TTable) {
    char g = guess;
    char upperbound =node->TotalTricks();
    char lowerbound = 0;
    while (lowerbound < upperbound) {
        char beta;
        (g == lowerbound) ? beta = g + 1 : beta = g;
        g = AlphaBetaMemoryIso(node, beta - 1, beta, TTable);
        (g < beta) ? upperbound = g : lowerbound = g;
    }
    return g;
}

char IncrementalAlphaBetaMemoryIso(Node* node, char alpha, char beta,int depth, std::vector<vectorNa>* TTable,std::unordered_map<uint32_t,uint32_t>* SuitRanks, std::vector<std::vector<uint32_t>>& bin_coeffs) {
    //fail soft ab search
    char val = 0;
    uint64_t key = 0;
    bool player = node->Player();
    if (node->IsTerminal()) {
        return node->Score();
    }
    if (node->Moves() % 2 == 0&& depth==0) {
        node->UpdateNodeKey();
        key = (player) ? node->AltKey() : node->GetNodeKey();
        uint32_t cards = key & _bzhi_u64(~0, 32);
        uint32_t colex = HalfColexer(cards, bin_coeffs);
        uint32_t suits = (key & (~0 ^ _bzhi_u64(~0, 32))) >> 32;
        uint32_t suit_rank = SuitRanks->at(suits);
        char value = (player) ? node->RemainingTricks() - TTable->at(colex).Get(suit_rank) :TTable->at(colex).Get(suit_rank);
        return value+node->Score();
    }
    else if (node->Player() == 0) {
        val = 0;
        std::vector<Action> actions = node->LegalActions();
        for (int i = 0; i < actions.size(); ++i) {
            node->ApplyAction(actions[i]);
            val = std::max(val,IncrementalAlphaBetaMemoryIso(node, alpha, beta,depth-1, TTable,SuitRanks,bin_coeffs));
            node->UndoAction(actions[i]);
            alpha = std::max(val, alpha);
            if (val >= beta) {
                break;
            }
        }
    }
    else if (node->Player() == 1) {
        val =node->TotalTricks();
        std::vector<Action> actions = node->LegalActions();
        for (int i = 0; i < actions.size(); ++i) {
            node->ApplyAction(actions[i]);
            val = std::min(val, IncrementalAlphaBetaMemoryIso(node, alpha, beta,depth-1, TTable,SuitRanks,bin_coeffs));
            node->UndoAction(actions[i]);
            beta = std::min(val, beta);
            if (val <= alpha) {
                break;
            }
        }
    }
    return val;
};


char IncrementalMTD(Node* node, char guess,int depth, std::vector<vectorNa>* TTable,std::unordered_map<uint32_t,uint32_t>* SuitRanks,std::vector<std::vector<uint32_t>>& bin_coeffs) {
    char g = guess;
    char upperbound = node->TotalTricks();
    char lowerbound = 0;
    while (lowerbound < upperbound) {
        char beta;
        (g == lowerbound) ? beta = g + 1 : beta = g;
        g = IncrementalAlphaBetaMemoryIso(node, beta - 1, beta,depth,TTable,SuitRanks, bin_coeffs);
        (g < beta) ? upperbound = g : lowerbound = g;
    }
    return g;
}
 std::vector<Node> GWhistGenerator(int num,unsigned int seed){
     //generates pseudorandom endgames//
     std::vector<Node> out;
     out.reserve(num);
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
         int sum = 0;
         std::vector<int> suit_lengths = {0,0,0,0};
         for(int j =0;j<kNumSuits-1;++j){
             int max = std::min(kNumRanks,2*kNumRanks-sum);
             int min = std::max(0,(j-1)*kNumRanks-sum);
             std::uniform_int_distribution<> distrib(min,max);
             suit_lengths[j] = distrib(g);
             sum+= suit_lengths[j];
         }
         suit_lengths[kNumSuits-1]=2*kNumRanks-sum;
         sum =0;
         for(int j =0;j<kNumSuits;++j){
             sum+=suit_lengths[j];
             if(suit_lengths[j]>kNumRanks){
                 throw;
             }
         }
         if(sum!= 2*kNumRanks){
             for(int j =0;j<suit_lengths.size();++j){
                 std::cout<<suit_lengths[j]<<" "<<std::endl;
             }
             throw;
         }
         int cum_sum =0;
         for (int j = 0; j < kNumSuits; ++j) {
             if (j == 0) {
                 suits[j] = _bzhi_u32(~0, suit_lengths[j]);
             }
             else {
                 suits[j] = (_bzhi_u32(~0, suit_lengths[j]+cum_sum)) ^ _bzhi_u32(~0,cum_sum);
                 //assert((suits[j] & suits[j - 1])== 0);
             }
             cum_sum+= suit_lengths[j];
         }
         out.push_back(Node(cards, suits, 0,false));
        #ifdef DEBUG
         std::cout << __builtin_popcount(cards) << " " << __builtin_popcount(suits[0]) + __builtin_popcount(suits[1]) + __builtin_popcount(suits[2]) + __builtin_popcount(suits[3]) << std::endl;
         std::cout << cards << " " << suits[0] << " " << suits[1] << " " << suits[2] << " " << suits[3] << std::endl;
        #endif

     }
     return out;
 }

 std::vector<vectorNa> InitialiseTTable(int size,std::vector<std::vector<uint32_t>>& bin_coeffs) {
     //initialises TTable for a certain depth//
     size_t suit_size = GenQuads(size).size();
     return std::vector<vectorNa>(bin_coeffs[2 * size][size], vectorNa(suit_size, 0));
 }

 std::vector<vectorNa> RetroSolver(int size_endgames,std::vector<vectorNa>* TTable,std::vector<std::vector<uint32_t>>& bin_coeffs) {
     //takes endgames solved to depth d-1 and returns endgames solved to depth d //
     std::vector<vectorNa> outTTable = InitialiseTTable(size_endgames, bin_coeffs);
     std::vector<uint32_t> suit_splits = GenQuads(size_endgames);
     std::unordered_map<uint32_t, uint32_t> SuitRanks;
     GenSuitRankingsRel(size_endgames-1,&SuitRanks);
     std::vector<int> combination;
     combination.reserve(size_endgames);
     for (int i = 0; i < size_endgames ; ++i) {
         combination.push_back(i);
     }
     bool control = true;
     int count = 0;
     while(control) {
         uint32_t cards =0;
         for(int i=0;i<combination.size();++i){
             cards = cards|(1<<combination[i]);
         }
         //#pragma omp parallel for
         for (int i = 0; i < suit_splits.size(); ++i) {
             std::array<uint32_t, kNumSuits> suit_arr;
             suit_arr[0] = _bzhi_u32(~0, suit_splits[i] & 0b1111);
             int sum = suit_splits[i] & 0b1111;
             for (int j = 1; j < kNumSuits; ++j) {
                 uint32_t mask = _bzhi_u32(~0, sum);
                 sum += (suit_splits[i] & (0b1111 << (4 * j)))>>4*j;
                 suit_arr[j] = _bzhi_u32(~0, sum);
                 suit_arr[j] = suit_arr[j] ^ mask;
             }
             Node node(cards, suit_arr, 0, false);
             char result = IncrementalMTD(&node, (size_endgames >> 1),2, TTable,&SuitRanks,bin_coeffs);
             outTTable[count].Set(i, result);
         }
         control = NextColex(combination,2*size_endgames);
         count++;
     }
     return outTTable;
 }

bool TestRetroSolve(int samples,int depth, uint32_t seed,std::vector<std::vector<uint32_t>>&bin_coeffs){
    //Tests endgame solution with TTable vs raw seach
    std::vector<Node> nodes = GWhistGenerator(samples,seed);
    std::vector<vectorNa> v;
    for(int i =1;i<=depth;++i){
        v=RetroSolver(i,&v,bin_coeffs);
    }
    std::unordered_map<uint32_t,uint32_t> SuitRanks ;
    GenSuitRankingsRel(depth,&SuitRanks);
    for (auto it = nodes.begin(); it != nodes.end(); ++it) {
        char abm_unsafe = IncrementalMTD(&*it,6,2*(kNumRanks-depth), &v, &SuitRanks, bin_coeffs);
        char abm_safe = AlphaBeta(&*it,0,kNumRanks);
        if(abm_unsafe!=abm_safe){
            return false;
        }
    }
    return true;
}

void StoreTTable(const std::string filename, const std::vector<vectorNa>& solution){
    //stores solution into a text file//
    std::ofstream file(filename);
    for(int i =0;i<solution.size();++i){
        for(int j=0;j<solution[i].size();++j){
            file.put(solution[i][j]);
        }
    }
    file.close();
}

std::vector<vectorNa> LoadTTable(const std::string filename, int depth,std::vector<std::vector<uint32_t>>& bin_coeffs){
    //loads solution from a text file into a vector for use//
    std::vector<vectorNa> v = InitialiseTTable(depth,bin_coeffs);
    std::ifstream file(filename,std::ios::binary);
    size_t length = v[0].size();
    char c;
    for(int i =0;i<v.size();++i){
        for(int j =0;j<length;++j){
            file.get(c);
            v[i].SetChar(j,c);
        }
    }
    file.close();
    return v;
}

bool TestTTableStorage(std::string filename, std::vector<vectorNa>& v,int depth,std::vector<std::vector<uint32_t>>& bin_coeffs){
    //Tests storage fidelity//
    StoreTTable(filename,v);
    std::vector<vectorNa> new_v = LoadTTable(filename,depth,bin_coeffs);
    for(int i =0;i<v.size();++i){
        for(int j =0;j<v[i].size();++j){
            if(v[i][j]!=new_v[i][j]){
                return false;
            }
        }
    }
    return true;
}
 //DONE //
 //MOVE ORDERING, STRATEGIC MOVE FUSION, ALPHA BETA PRUNING, TRANSPOSITION TABLE, RANDOM ENDGAME GENERATION//
 //CORRECT ALPHABETAMEMORY SEARCH//
 //SEARCH TAKING ADVANTAGE OF PLAYER ISOMORPHISM//
 //RETROGRADE ANALYSIS//
// SAVING& LOADING TTABLES TO THE COMPUTER//
 //
// TO DO//
// CODE CLEANUP/REVIEW//
//REMOVAL OF DEPRECATED FUNCTIONS//
//SOME BENCHMARKING (10,000 IN 1400MS->0.14MS A GAME) FOR DEPTH 10 TTABLE  GENERATES DEPTH 10 TABLE IN 400 SECONDS//
// (10,000->0.04ms A GAME FOR DEPTH 11 TTABLE//
//RAN INTO ISSUE CONVERTING 11 TO 12, INVESTIGATE//
