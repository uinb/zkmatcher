include "../circomlib/poseidon.circom";

template Hasher() {
    signal input left;
    signal input right;
    signal output hash;

    component hasher = Poseidon(2);
    left ==> hasher.inputs[0];
    right ==> hasher.inputs[1];
    hash <== hasher.out;
}

template SMTVerifier(height) {
    signal input root;
    signal input key;
    signal input value;
    signal input path[height];

    component hasher[height];
    for (i=0; i<height; i++) {
        hasher[i] = Hasher();
        if (i==0) {
           hasher[i].left <== key;
           hasher[i].right <== value;
        } else {
           // FIXME we messed up the order
           hasher[i].left <== hasher[i-1].hash;
           hasher[i].right <== path[i-1];
        }
    }
    component check_root = ForceEqualIfEnabled();
    check_root.enabled <== enabled;
    check_root.in[0] <== hasher[height-1].hash;
    check_root.in[1] <== root;
}