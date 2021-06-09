include "../circomlib/comparators.circom";
include "../circomlib/gates.circom";
include "../circomlib/poseidon.circom";
include "sparse_merkle_tree.circom";

/*
* TODO: merkle root step-by-step
*
* merkle tree:
*   k -> hash((v!=0)*k, v) where k, v in :
*     1. hash(hash(b,q), ask_or_bid); hash(size, best)
*     2. hash(order_id); hash(owner, amount, price)
*     3. hash(account, currency); hash(tradable, frozen)
*/
template TradeLimitCmd() {
    signal input new_merkle_root;

    signal input base_currency;
    signal input quote_currency;

    // ask -- 0
    // bid -- 1
    signal input ask_or_bid;
    // tape size
    signal input oppo_size;
    signal input self_size;
    // next maker
    signal input next_best_price;
    signal input orderbook_self_path[256];
    signal input orderbook_oppo_path[256];

    signal input taker_order_id;
    signal input taker_account;
    signal input taker_price;
    signal input taker_amount; // before traded
    signal input taker_order_path[256];

    signal input taker_fee;
    signal input taker_quote_tradable;
    signal input taker_quote_frozen;
    signal input taker_quote_path[256];
    signal input taker_base_tradable;
    signal input taker_base_frozen;
    signal input taker_base_path[256];

    signal input maker_order_id;
    signal input maker_account;
    signal input maker_price;
    signal input maker_amount; // before traded
    signal input maker_order_path[256];

    signal input maker_fee;
    signal input maker_quote_tradable;
    signal input maker_quote_frozen;
    signal input maker_quote_path[256];
    signal input maker_base_tradable;
    signal input maker_base_frozen;
    signal input maker_base_path[256];

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

    // taker >= best when bid or taker <= best when ask, output 1 or 0
    component or = OR();
    or.a <== and0.out;
    or.b <== and1.out;

    // we need ensure maker exists
    component maker_not_exists = IsZero();
    maker_not_exists.in <== maker_order_id;
    component maker_exists = NOT();
    maker_exists.in <== maker_not_exists.out;

    // final gate
    component final_condition = AND();
    final_condition.a <== maker_exists.out;
    final_condition.b <== or.out;

    // min(taker, maker)
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

    // final traded amount
    signal traded;
    traded <-- final_condition.out * a;
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
    component is_oppo_empty = IsZero();
    is_oppo_empty.in <== oppo_size - traded;
    component is_oppo_not_empty = NOT();
    is_oppo_not_empty.in <== is_oppo_empty.out;
    c1v.inputs[1] <== is_oppo_not_empty.out * next_best_price;

    // c1kv = hash(c1k, c1v)
    component c1kv = Poseidon(2);
    c1kv.inputs[0] <== c1k.out * is_oppo_not_empty.out;
    c1kv.inputs[1] <== c1v.out;

    component c1_verifier = SMTVerifier(256);
    c1_verifier.key <== c1k.out;
    c1_verifier.value <== c1kv.out
    c1_verifier.root <== new_merkle_root;
    for (i=0; i<256; i++) c1_verifier.path[i] <== orderbook_oppo_path[i];

    // c2k = hash(maker_order_id)
    component c2k = Poseidon(1);
    c2k.inputs[0] <== maker_order_id;

    // c2v = hash((maker_remain!=0)*maker_account, maker_remain, (maker_remain!=0)*maker_price);
    component c2v = Poseidon(3);
    component is_maker_zero = IsZero();
    is_maker_zero.in <== maker_amount - traded;
    component is_maker_not_zero = NOT();
    is_maker_not_zero.in <== is_maker_zero.out;
    c2v.inputs[0] <== maker_account * is_maker_not_zero.out;
    c2v.inputs[1] <== maker_remain;
    c2v.inputs[2] <== maker_price * is_maker_not_zero.out;

    // c2kv = hash(c2k, c2v)
    component c2kv = Poseidon(2);
    c2kv.inputs[0] <== c2k.out * is_maker_not_zero.out;
    c2kv.inputs[1] <== c2v.out;

    component c2_verifier = SMTVerifier(256);
    c2_verifier.key <== c2k.out;
    c2_verifier.value <== c2kv.out
    c2_verifier.root <== new_merkle_root;
    for (i=0; i<256; i++) c2_verifier.path[i] <== maker_order_path[i];

    // c3k = hash(taker_order_id)
    component c3k = Poseidon(1);
    c3k.inputs[0] <== taker_order_id;

    // c3v = hash((taker_remain!=0 and traded==0)*taker_account, (taker_remain!=0 and traded==0)*taker_remain, (taker_remain!=0 and traded==0)*taker_price)
    component c3v = Poseidon(3);
    component is_taker_zero = IsZero();
    is_taker_zero.in <== taker_amount - traded;
    component is_taker_not_zero = NOT();
    is_taker_not_zero.in <== is_taker_zero.out;
    component is_traded_zero = IsZero();
    is_traded_zero.in <== traded;
    component should_place = AND();
    should_place.a <== is_maker_not_zero.out;
    should_place.b <== is_traded_zero.out;
    c3v.inputs[0] <== taker_account * should_place.out;
    c3v.inputs[1] <== taker_remain * should_place.out;
    c3v.inputs[2] <== taker_price * should_place.out;

    // c3kv = hash(c3k, c3v)
    component c3kv = Poseidon(2);
    c3kv.inputs[0] <== c3k.out * should_place.out;
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

    // c4v = hash(self_size+should_place*taker_remain, should_place*taker_price)
    component c4v = Poseidon(2);
    signal delta;
    delta <-- should_place.out * taker_remain;
    c4v.inputs[0] <== self_size + delta;
    c4v.inputs[1] <== should_place.out * taker_price;

    component c4kv = Poseidon(2);
    c4kv.inputs[0] <== c4k.out;
    c4kv.inputs[1] <== c4v.out;

    component c4_verifier = SMTVerifier(256);
    c4_verifier.key <== c4k.out;
    c4_verifier.value <== c4kv.out
    c4_verifier.root <== new_merkle_root;
    for (i=0; i<256; i++) c4_verifier.path[i] <== orderbook_self_path[i];

    //taker_base: +tradable(traded * (1 - taker_fee)) or +frozen(should_place * remain)
    component taker_base = AssetsValidator();
    taker_base.account_id <== taker_account;
    taker_base.assets_id <== base_currency;
    signal egbt;
    egbt <== traded * taker_fee;
    signal tgb;
    tgb <== traded - egbt;
    signal ifb_tgb;
    ifb_tgb <== tgb * ask_or_bid;
    taker_base.tradable <== taker_base_tradable + ifb_tgb;
    signal trb;
    trb <== should_place.out * taker_remain;
    signal ifa_trb;
    ifa_trb <== trb * not.out;
    taker_base.frozen <== taker_base_frozen + ifa_trb;
    taker_base.merkle_root <== new_merkle_root;
    for (i=0; i<256; i++) taker_base.path[i] <== taker_base_path[i];

    //maker_base: -frozen(traded) or +tradable(traded * (1 - maker_fee))
    component maker_base = AssetsValidator();
    maker_base.account_id <== maker_account;
    maker_base.assets_id <== base_currency;
    signal ifb_traded;
    ifb_traded <== ask_or_bid * traded;
    maker_base.frozen <== taker_base_frozen - ifb_traded;
    signal egbm;
    egbm <== traded * maker_fee;
    signal mgb;
    mgb <== traded - egbm;
    signal ifa_mgb;
    ifa_mgb <== mgb * not.out;
    maker_base.tradable <== maker_base_tradable + ifa_mgb;
    maker_base.merkle_root <== new_merkle_root;
    for (i=0; i<256; i++) maker_base.path[i] <== maker_base_path[i];

    //taker_quote: +frozen(should_place * remain * price) or +tradable(traded * price * (1 - taker_fee))
    component taker_quote = AssetsValidator();
    taker_quote.account_id <== taker_account;
    taker_quote.assets_id <== quote_currency;
    signal frozen_vol;
    frozen_vol <== taker_remain * taker_price;
    signal should_frozen_vol;
    should_frozen_vol <== should_place.out * frozen_vol;
    signal ifb_frozen_vol;
    ifb_frozen_vol <== ask_or_bid * should_frozen_vol;
    taker_quote.frozen <== taker_quote_frozen + ifb_frozen_vol;
    signal vol;
    tgq <== traded * price;
    signal egqt;
    egqt <== tgq * taker_fee;
    signal tgq;
    tgq <== vol - egqt;
    signal ifa_tgq;
    ifa_tgq <== tgq * not.out;
    taker_quote.tradable <== taker_quote_tradable + ifa_tgq;
    taker_quote.merkle_root <== new_merkle_root;
    for (i=0; i<256; i++) taker_quote.path[i] <== taker_quote_path[i];

    //maker_quote: +tradable(traded * price * (1 - maker_fee)) or -frozen(traded * price)
    component maker_quote = AssetsValidator();
    maker_quote.account_id <== maker_account;
    maker_quote.assets_id <== quote_currency;
    signal maker_vol;
    maker_vol <== traded * price;
    signal quote_fee;
    quote_fee <= maker_vol * maker_fee;
    signal vol_fee_excluded;
    vol_fee_excluded <== vol - quote_fee;
    signal ifb_to_maker;
    ifb_to_maker_quote <== vol_fee_excluded * ask_or_bid;
    maker_quote.tradable <== maker_quote_tradable + ifb_to_maker_quote;
    ifa_from_maker_quote <== vol * not.out;
    maker_quote.frozen <== maker_quote_frozen - ifa_from_maker_quote;
    maker_quote.merkle_root <== new_merkle_root;
    for (i=0; i<256; i++) maker_quote.path[i] <== maker_quote_path[i];
}

/*
*   hash(account, currency) -> hash(hash(account, currency), hash(tradable, frozen))
*/
template AssetsValidator() {
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
    value.inputs[1] <== frozen;

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