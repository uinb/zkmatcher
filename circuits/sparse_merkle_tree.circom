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
    var i;
    for (i=0; i<height; i++) {
        hasher[i] = Hasher();
        if (i==0) {
           hasher[i].left <== key;
           hasher[i].right <== value;
        } else {
           hasher[i].left <== hasher[i-1].hash;
           hasher[i].right <== path[i-1];
        }
    }
    component check_root = ForceEqualIfEnabled();
    check_root.enabled <== 1;
    check_root.in[0] <== hasher[height-1].hash;
    check_root.in[1] <== root;
}

template SMT(height) {
    signal input old_root;
    signal input key;
    signal input old_value;
    signal input new_value;
    signal input path[height];
    signal output new_root;

    component verifier = SMTVerifier(height);
    verifier.root <== old_root;
    verifier.key <== key;
    verifier.value <== old_value;
    var i;
    for (i=0;i<height;i++) verifier.path[i] <== path[i];
    component hasher[height];
    var i;
    for (i=0; i<height; i++) {
        hasher[i] = Hasher();
        if (i==0) {
           hasher[i].left <== key;
           hasher[i].right <== new_value;
        } else {
           hasher[i].left <== hasher[i-1].hash;
           hasher[i].right <== path[i-1];
        }
    }
    new_root <== hasher[height-1].hash;
}