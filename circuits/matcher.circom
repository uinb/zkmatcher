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

template TradableAssetsValidator() {
    signal input account_id;
    signal input assets;
    signal input tradable;
    signal input merkle_root;
    signal input path[256];

    component account = Hasher();
    account.left <== account_id;
    account.right <== assets;
    component leaf = Hasher();
    leaf.left <== account.hash;
    leaf.right <== tradable;
    component smt = SMTVerifier(256);
    smt.root <== merkle_root;
    smt.key <== leaf.hash;
    smt.value <== assets;
    var i;
    for (i=0; i<256; i++) smt.path[i] <== path[i];
}

template OrderbookValidator() {
    signal input pair;
    signal input ask_or_bid;
    signal input size;
    signal input best_price;
    signal input size_path[256];
    signal input price_path[256];
    signal input merkle_root;

    component size_leaf = Hasher();
    size_leaf.left <== pair;
    size_leaf.right <== ask_or_bid;
    component smt0 = SMTVerifier(256);
    smt0.root <== merkle_root;
    smt0.key <== size_leaf.hash;
    smt0.value <== size;
    var i;
    for (i=0; i<256; i++) smt0.path[i] <== size_path[i];

    component price_leaf = Hasher();
    price_leaf.left <== pair;
    price_leaf.right <== ask_or_bid + 2;
    component smt1 = SMTVerifier(256);
    smt1.root <== merkle_root;
    smt1.key <== price_leaf.hash;
    smt1.value <== best_price;
    for (i=0; i<256; i++) smt1.path[i] <== price_path[i];
}

// template Matcher() {
//     signal input account_id;
//     signal input pair;
// }

component main = OrderbookValidator();