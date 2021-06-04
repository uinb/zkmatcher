include "../circomlib/comparators.circom";
include "../circomlib/gates.circom";
include "sparse_merkle_tree.circom";

/*
* merkle_tree: node_v: hash((v!=0)*k, v)
*   hash(hash(b,q), not(ask_or_bid)) -> hash(new_size, (new_size!=0)*new_best_price) //hash2
*   hash(hash(b,q), maker_order_id) -> hash((maker_remain!=0)*maker_account, (maker_remain!=0)*maker_price, maker_remain) //hash3
*   hash(hash(b,q), taker_order_id) -> hash((taker_remain!=0 and maker_remain!=0)*taker_account, (taker_remain!=0 and maker_remain!=0)*taker_price, taker_remain) //hash3
*   hash(hash(b,q), ask_or_bid) -> hash(new_size, (new_size!=0)*taker_price) //hash2
*/
template TradeLimitCmd() {
    signal input new_merkle_root;

    signal input base_currency;
    signal input quote_currency;

    // ask -- 0
    // bid -- 1
    signal input ask_or_bid;
    signal input oppo_size;
    signal input size;
    signal input orderbook_ask_path[256];
    signal input orderbook_bid_path[256];

    signal input taker_order_id;
    signal input taker_account;
    signal input taker_price;
    signal input taker_amount;
    signal input taker_order_path[256];

    signal input maker_order_id;
    signal input maker_account;
    signal input maker_price;
    signal input maker_amount;
    signal input maker_order_path[256];

    signal output trade_amount;
    signal output trade_price;
    signal output taker_remain;
    signal output maker_remain;

    // if bid1, ge
    component pge = GreaterEqThan(128);
    pge.in[0] <== taker_price;
    pge.in[1] <== maker_price;
    component and0 = AND();
    and0.a <== pge.out;
    and0.b <== ask_or_bid;
    // if ask0, le
    component ple = LessEqThan(128);
    ple.in[0] <== taker_price;
    ple.in[1] <== maker_price;
    component not = NOT();
    not.int <== ask_or_bid;
    component and1 = AND();
    and1.a <== not.out;
    and1.b <== ple.out;

    component or = OR();
    or.a <== and0.out;
    or.b <== and1.out;

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
    
    trade_amount <== or.out * a;
    trade_price <== or.out * maker_price;
    taker_remain <== taker_amount - trade_amount;
    maker_remain <== maker_amount - trade_amount;
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