include "../circomlib/comparators.circom";
include "sparse_merkle_tree.circom";

template BidLimitCmd() {
    signal input taker_price;
    signal input taker_amount;
    signal input maker_price;
    signal input maker_amount;
    signal output trade_amount;
    signal output trade_price;

    component age = GreaterEqThan(128);
    age.in[0] <== taker_amount;
    age.in[1] <== maker_amount;
    signal v1;
    v1 <-- maker_amount * age.out;

    component alt = LessThan(128);
    alt.in[0] <== taker_amount;
    alt.in[1] <== maker_amount;
    signal v2;
    v2 <-- taker_amount * alt.out;

    signal a;
    a <-- v1 + v2;
    
    component pge = GreaterEqThan(128);
    pge.in[0] <== taker_price;
    pge.in[1] <== maker_price;
    trade_amount <== pge.out * a;
    trade_price <== pge.out * maker_price;
}

template AskLimitCmd() {
    signal input taker_price;
    signal input taker_amount;
    signal input maker_price;
    signal input maker_amount;
    signal output trade_amount;
    signal output trade_price;

    component age = GreaterEqThan(128);
    age.in[0] <== taker_amount;
    age.in[1] <== maker_amount;
    signal v1;
    v1 <-- maker_amount * age.out;

    component alt = LessThan(128);
    alt.in[0] <== taker_amount;
    alt.in[1] <== maker_amount;
    signal v2;
    v2 <-- taker_amount * alt.out;

    signal a;
    a <-- v1 + v2;
    
    component pge = LessEqThan(128);
    pge.in[0] <== taker_price;
    pge.in[1] <== maker_price;
    trade_amount <== pge.out * a;
    trade_price <== pge.out * maker_price;
}

template orderbook(height) {
    signal input pair;
    signal input ask_size;
    // signal input bid_size;
    // signal input best_ask_price;
    // signal input best_bid_price;
    signal input siblings[height];
    signal output merkle_root;

    component ask_size_addr = Hasher();
    ask_size_addr.left <== pair;
    // TODO undefined
    ask_size_addr.right <== 0;
    // component smt = SMTVerifier(height);
    smt.root <== merkle_root;
    smt.key <== ask_size_addr.hash;
    smt.value <== ask_size;
    smt.path <== siblings;
}

// template assets(merkle_level) {
//     signal input account;
//     signal input tradable;
//     signal input frozen;
//     signal input siblings[merkle_level];
//     signal output merkle_root;
// }


component main = BidLimitCmd();