include "../circomlib/comparators.circom";
include "../circomlib/gates.circom";
include "../circomlib/poseidon.circom";
include "sparse_merkle_tree.circom";

/*
* TODO: merkle root step-by-step
*
* merkle tree:
*   k -> hash((v!=0)*k, v) where k, v in:
*     1. hash(hash(b,q), ask_or_bid); hash(size, best)
*     2. hash(order_id); hash(owner, amount, price, ask_or_bid + 1)
*     3. hash(account, currency); hash(tradable, frozen)
*   update order:
*     1. taker account, old_root -> root1
*     2. oppo tape, root1 -> root2
*     3. self tape, root2 -> root3
*     4. maker order, root3 -> root4
*     5. taker order, root4 -> root5
*     6. maker base account, root5 -> root6
*     7. maker quote account, root6 -> root7
*     8. taker base account, root7 -> root8
*     9. taker quote account, root8 -> new_root
*/
template TradeLimitCmd() {
    signal input enable;
    signal input old_merkle_root;
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
    // TODO mark as order=5
    signal input orderbook_self_path[256];
    // TODO order=2
    signal input orderbook_oppo_path[256];

    signal input taker_order_id;
    signal input taker_account;
    signal input taker_price;
    signal input taker_amount;
    // TODO order=4
    signal input taker_order_path[256];

    signal input taker_fee;
    signal input taker_quote_tradable;
    signal input taker_quote_frozen;
    signal input taker_base_tradable;
    signal input taker_base_frozen;
    // TODO order=1
    signal input taker_account_path[256];
    // TODO order=7
    signal input taker_account_clear_path[256];

    signal input maker_order_id;
    signal input maker_account;
    signal input maker_price;
    signal input maker_amount;
    // TODO order=3
    signal input maker_order_path[256];

    signal input maker_fee;
    signal input maker_quote_tradable;
    signal input maker_quote_frozen;
    signal input maker_base_tradable;
    signal input maker_base_frozen;
    // TODO order=6
    signal input maker_account_clear_path[256];

    signal taker_remain;
    signal maker_remain;

    // ======== basic parameters ========
    var i;
    component bid_or_ask = NOT();
    bid_or_ask.in <== ask_or_bid;
    component bq = Poseidon(2);
    bq.inputs[0] <== base_currency;
    bq.inputs[1] <== quote_currency;

    // taker frozen currency
    signal taker_frozen_currency_ifb;
    taker_frozen_currency_ifb <== quote_currency * ask_or_bid;
    signal taker_frozen_currency_ifa;
    taker_frozen_currency_ifa <== base_currency * bid_or_ask.out;
    signal taker_frozen_currency;
    taker_frozen_currency <== taker_frozen_currency_ifb + taker_frozen_currency_ifa;

    // maker frozen currency
    signal maker_frozen_currency_ifb;
    maker_frozen_currency_ifb <== base_currency * ask_or_bid;
    signal maker_frozen_currency_ifa;
    maker_frozen_currency_ifa <== quote_currency * bid_or_ask.out;
    signal maker_frozen_currency;
    maker_frozen_currency <== maker_frozen_currency_ifb + maker_frozen_currency_ifa;

    // taker account
    signal taker_pay_tradable_account;
    signal taker_pay_frozen_account;
    signal taker_rev_tradable_account;
    signal taker_rev_frozen_account;

    signal taker_pay_tradable_account_ifb;
    signal taker_pay_tradable_account_ifa;
    signal taker_pay_frozen_account_ifb;
    signal taker_pay_frozen_account_ifa;
    signal taker_rev_tradable_account_ifb;
    signal taker_rev_tradable_account_ifa;
    signal taker_rev_frozen_account_ifb;
    signal taker_rev_frozen_account_ifa;

    taker_pay_tradable_account_ifb <== taker_quote_tradable * ask_or_bid;
    taker_pay_frozen_account_ifb <== taker_quote_frozen * ask_or_bid;
    taker_rev_tradable_account_ifb <== taker_base_tradable * ask_or_bid;
    taker_rev_frozen_account_ifb <== taker_base_frozen * ask_or_bid;
    taker_pay_tradable_account_ifa <== taker_base_tradable * bid_or_ask.out;
    taker_pay_frozen_account_ifa <== taker_base_frozen * bid_or_ask.out;
    taker_rev_tradable_account_ifa <== taker_quote_tradable * bid_or_ask.out;
    taker_rev_frozen_account_ifa <== taker_quote_frozen * bid_or_ask.out;
    taker_pay_tradable_account <== taker_pay_tradable_account_ifb + taker_pay_tradable_account_ifa;
    taker_pay_frozen_account <== taker_pay_frozen_account_ifb + taker_pay_frozen_account_ifa;
    taker_rev_tradable_account <== taker_rev_tradable_account_ifb + taker_rev_tradable_account_ifa;
    taker_rev_frozen_account <== taker_rev_frozen_account_ifb + taker_rev_frozen_account_ifa;

    // maker account;
    signal maker_rev_tradable_account;
    signal maker_rev_frozen_account;
    signal maker_pay_tradable_account;
    signal maker_pay_frozen_account;

    signal maker_rev_tradable_account_ifb;
    signal maker_rev_tradable_account_ifa;
    signal maker_rev_frozen_account_ifb;
    signal maker_rev_frozen_account_ifa;
    signal maker_pay_tradable_account_ifb;
    signal maker_pay_tradable_account_ifa;
    signal maker_pay_frozen_account_ifb;
    signal maker_pay_frozen_account_ifa;

    maker_rev_tradable_account_ifb <== maker_quote_tradable * ask_or_bid;
    maker_rev_frozen_account_ifb <== maker_quote_frozen * ask_or_bid;
    maker_pay_tradable_account_ifb <== maker_base_tradable * ask_or_bid;
    maker_pay_frozen_account_ifb <== maker_base_frozen * ask_or_bid;
    maker_rev_tradable_account_ifa <== maker_base_tradable * bid_or_ask.out;
    maker_rev_frozen_account_ifa <== maker_base_frozen * bid_or_ask.out;
    maker_pay_tradable_account_ifa <== maker_quote_tradable * bid_or_ask.out;
    maker_pay_frozen_account_ifa <== maker_quote_frozen * bid_or_ask.out;
    maker_rev_tradable_account <== maker_rev_tradable_account_ifb + maker_rev_tradable_account_ifa;
    maker_rev_frozen_account <== maker_rev_frozen_account_ifb + maker_rev_frozen_account_ifa;
    maker_pay_tradable_account <== maker_pay_tradable_account_ifb + maker_pay_tradable_account_ifa;
    maker_pay_frozen_account <== maker_pay_frozen_account_ifb + maker_pay_frozen_account_ifa;

    // taker frozen amount
    signal taker_vol;
    taker_vol <== taker_amount * taker_price;
    signal taker_frozen_ifb;
    taker_frozen_ifb <== taker_vol * ask_or_bid;
    signal taker_frozen_ifa;
    taker_frozen_ifa <== taker_amount * bid_or_ask.out;
    signal taker_frozen;
    taker_frozen <== taker_frozen_ifb + taker_frozen_ifa;

    // maker frozen amount
    signal maker_frozen_ifb;
    maker_frozen_ifb <== maker_amount * ask_or_bid;
    signal maker_vol;
    maker_vol <== maker_amount * maker_price;
    signal maker_frozen_ifa;
    maker_frozen_ifa <== maker_vol * bid_or_ask.out;
    signal maker_frozen;
    maker_frozen <== maker_frozen_ifb + maker_frozen_ifa;

    //======== taker: tradable_base>=frozen_amount or trablable_quote>=frozen_amount ========
    component taker_tq_ge = GreaterEqThan(128);
    taker_tq_ge.in[0] <== taker_quote_tradable * ask_or_bid;
    taker_tq_ge.in[1] <== taker_frozen_ifb;
    component taker_tb_ge = GreaterEqThan(128);
    taker_tb_ge.in[0] <== taker_base_tradable * bid_or_ask.out;
    taker_tb_ge.in[1] <== taker_frozen_ifa;
    component tqtb = AND();
    tqtb.a <== taker_tq_ge.out;
    tqtb.b <== taker_tb_ge.out;
    component check_taker = ForceEqualIfEnabled();
    check_taker.enabled <== enable;
    check_taker.in[0] <== tqtb.out;
    check_taker.in[1] <== 1;

    //======== maker: freezed_base>=frozen_amount or freezed_quote>=frozen_amount ========
    component maker_fb_ge = GreaterEqThan(128);
    maker_fb_ge.in[0] <== maker_base_frozen * ask_or_bid;
    maker_fb_ge.in[1] <== maker_frozen_ifb;
    component maker_fq_ge = GreaterEqThan(128);
    maker_fq_ge.in[0] <== maker_quote_frozen * bid_or_ask.out;
    maker_fq_ge.in[1] <== maker_frozen_ifa;
    component mqmb = AND();
    mqmb.a <== maker_fb_ge.out;
    mqmb.b <== maker_fq_ge.out;
    component check_maker = ForceEqualIfEnabled();
    check_maker.enabled <== enable;
    check_maker.in[0] <== mqmb.out;
    check_maker.in[1] <== 1;

    //======== calculate root1 after frezze the taker ========
    component taker_frozen_account = Poseidon(2);
    taker_frozen_account.inputs[0] <== taker_account;
    taker_frozen_account.inputs[1] <== taker_frozen_currency;
    component taker_claimed_account_val = Poseidon(2);
    taker_claimed_account_val.inputs[0] <== taker_pay_tradable_account;
    taker_claimed_account_val.inputs[1] <== taker_pay_frozen_account;
    component taker_updated_account_val = Poseidon(2);
    taker_updated_account_val.inputs[0] <== taker_pay_tradable_account - taker_frozen;
    taker_updated_account_val.inputs[1] <== taker_pay_frozen_account + taker_frozen;
    component root1 = SMT(256);
    root1.old_root <== old_merkle_root;
    root1.key <== taker_frozen_account.out;
    root1.old_value <== taker_claimed_account_val.out;
    root1.new_value <== taker_updated_account_val.out;
    for (i=0; i<256; i++) root1.path[i] <== taker_account_path[i];

    //======== calculate the trade amount ========
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
    component and1 = AND();
    and1.a <== ple.out;
    and1.b <== bid_or_ask.out;
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

    //======== update oppo tape ========
    // c1k = hash(hash(b,q), not(ask_or_bid))
    component c1k = Poseidon(2);
    c1k.inputs[0] <== bq.out;
    c1k.inputs[1] <== bid_or_ask.out;

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

    // root1 --> root2
    // component root2 = SMT(256);
    // root2.old_root <== root1.new_root;
    // root2.key <== c1k.out;
    // root2.old_value <== ;
    // root2.new_value <== ;
    // for (i=0; i<256; i++) root2.path[i] <== orderbook_oppo_path[i];
    
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