include "../circomlib/comparators.circom";
include "../circomlib/gates.circom";
include "../circomlib/poseidon.circom";
include "sparse_merkle_tree.circom";

/*
* merkle_tree: node_v: hash((v!=0)*k, v)
*   hash(hash(b,q), not(ask_or_bid)) -> hash(new_size, (new_size!=0)*new_best_price)
*   hash(hash(b,q), maker_order_id) -> hash((maker_remain!=0)*maker_account, (maker_remain!=0)*maker_price, maker_remain)
*   hash(hash(b,q), taker_order_id) -> hash((taker_remain!=0 and maker_remain!=0)*taker_account, (taker_remain!=0 and maker_remain!=0)*taker_price, taker_remain)
*   hash(hash(b,q), ask_or_bid) -> hash(new_size, (new_size!=0)*taker_price)
*/
template TradeLimitCmd() {
    signal input new_merkle_root;

    signal input base_currency;
    signal input quote_currency;

    // ask -- 0
    // bid -- 1
    signal input ask_or_bid;
    signal input oppo_size;
    signal input self_size;
    signal input next_best_price;
    signal input orderbook_self_path[256];
    signal input orderbook_oppo_path[256];

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

    signal taker_remain;
    signal maker_remain;

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
    not.in <== ask_or_bid;
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

    signal traded;
    traded <-- or.out * a;
    taker_remain <== taker_amount - traded;
    maker_remain <== maker_amount - traded;

    var i;
    component bq = Poseidon(2);
    bq.inputs[0] <== base_currency;
    bq.inputs[1] <== quote_currency;

    // c1k = hash(hash(b,q), not(ask_or_bid))
    component c1k = Poseidon(2);
    c1k.inputs[0] <== bq.out;
    c1k.inputs[1] <== not.out;

    // c1v = hash(oppo_size - traded, is_not_zero(oppo_size - traded) * next_best_price)
    component c1v = Poseidon(2);
    c1v.inputs[0] <== oppo_size - traded;
    component is_zero = IsZero();
    is_zero.in <== oppo_size - traded;
    component is_not_zero = NOT();
    is_not_zero.in <== is_zero.out;
    c1v.inputs[1] <== is_not_zero.out * next_best_price;

    // c1kv = hash(c1k, c1v)
    component c1kv = Poseidon(2);
    c1kv.inputs[0] <== c1k.out * is_not_zero.out;
    c1kv.inputs[1] <== c1v.out;

    component c1_verifier = SMTVerifier(256);
    c1_verifier.key <== c1k.out;
    c1_verifier.value <== c1kv.out
    c1_verifier.root <== new_merkle_root;
    for (i=0; i<256; i++) c1_verifier.path[i] <== orderbook_oppo_path[i];

    // c2k = hash(hash(b,q), maker_order_id)
    component c2k = Poseidon(2);
    c2k.inputs[0] <== bq.out;
    c2k.inputs[1] <== maker_order_id;

    // c2v = hash((maker_remain!=0)*maker_account, (maker_remain!=0)*maker_price, maker_remain);
    component c2v = Poseidon(3);
    component is_maker_zero = IsZero();
    is_maker_zero.in <== maker_amount - traded;
    component is_maker_not_zero = NOT();
    is_maker_not_zero.in <== is_maker_zero.out;
    c2v.inputs[0] <== maker_account * is_maker_not_zero.out;
    c2v.inputs[1] <== maker_price * is_maker_not_zero.out;
    c2v.inputs[2] <== maker_remain;

    // c2kv = hash(c2k, c2v)
    component c2kv = Poseidon(2);
    c2kv.inputs[0] <== c2k.out;
    c2kv.inputs[1] <== c2v.out;

    component c2_verifier = SMTVerifier(256);
    c2_verifier.key <== c2k.out;
    c2_verifier.value <== c2kv.out
    c2_verifier.root <== new_merkle_root;
    for (i=0; i<256; i++) c2_verifier.path[i] <== maker_order_path[i];

    // c3k = hash(hash(b,q), taker_order_id)
    component c3k = Poseidon(2);
    c3k.inputs[0] <== bq.out;
    c3k.inputs[1] <== taker_order_id;

    // c3v = hash((taker_remain!=0 and maker_remain!=0)*taker_account, (taker_remain!=0 and maker_remain!=0)*taker_price, (taker_remain!=0 and maker_remain!=0)*taker_remain)
    component c3v = Poseidon(3);
    component is_taker_zero = IsZero();
    is_taker_zero.in <== taker_amount - traded;
    component is_taker_not_zero = NOT();
    is_taker_not_zero.in <== is_taker_zero.out;
    component both_remain = AND();
    both_remain.a <== is_maker_not_zero.out;
    both_remain.b <== is_taker_not_zero.out;
    c3v.inputs[0] <== taker_account * both_remain.out;
    c3v.inputs[1] <== taker_price * both_remain.out;
    c3v.inputs[2] <== taker_remain * both_remain.out;

    // c3kv = hash(c3k, c3v)
    component c3kv = Poseidon(2);
    c3kv.inputs[0] <== c3k.out;
    c3kv.inputs[1] <== c3v.out;

    component c3_verifier = SMTVerifier(256);
    c3_verifier.key <== c3k.out;
    c3_verifier.value <== c3kv.out
    c3_verifier.root <== new_merkle_root;
    for (i=0; i<256; i++) c3_verifier.path[i] <== taker_order_path[i];

    // c4k = hash(hash(b,q), ask_or_bid)
    component c4k = Poseidon(2);
    c4k.inputs[0] <== bq.out;
    c4k.inputs[1] <== ask_or_bid;

    // c4v = hash(self_size+(taker_remain!=0 and maker_remain!=0)*taker_remain, (taker_remain!=0 and maker_remain!=0)*taker_price)
    component c4v = Poseidon(2);
    signal delta;
    delta <-- both_remain.out * taker_remain;
    c4v.inputs[0] <== self_size + delta;
    c4v.inputs[1] <== both_remain.out * taker_price;

    component c4kv = Poseidon(2);
    c4kv.inputs[0] <== c4k.out;
    c4kv.inputs[1] <== c4v.out;

    component c4_verifier = SMTVerifier(256);
    c4_verifier.key <== c4k.out;
    c4_verifier.value <== c4kv.out
    c4_verifier.root <== new_merkle_root;
    for (i=0; i<256; i++) c4_verifier.path[i] <== orderbook_self_path[i];
}

/*
*   hash(account_id, assets_id) -> hash(hash(account_id, assets_id), hash(tradable, frozen))
*/
template TradableAssetsValidator() {
    signal input account_id;
    signal input assets_id;
    signal input tradable;
    signal input frozen;
    signal input merkle_root;
    signal input path[256];

    component key = Poseidon(2);
    key.inputs[0] <== account_id;
    key.inputs[1] <== assets_id;

    component value = Poseidon(2);
    value.inputs[0] <== tradable;
    value.inputs[1] <== fronzen;

    component kv = Poseidon(2);
    kv.inputs[0] <== key.out;
    kv.inputs[1] <== value.out;

    component smt = SMTVerifier(256);
    smt.root <== merkle_root;
    smt.key <== key.out;
    smt.value <== kv.out;
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

component main = TradeLimitCmd();