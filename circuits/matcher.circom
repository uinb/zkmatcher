include "../circomlib/comparators.circom";

template bid_limit() {
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

template ask_limit() {
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

component main = bid_limit();