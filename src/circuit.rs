use anyhow::Result;
use dusk_bls12_381::BlsScalar;
use dusk_jubjub::{JubJubAffine, GENERATOR_EXTENDED, GENERATOR_NUMS_EXTENDED};
use dusk_pki::Ownable;
use dusk_plonk::constraint_system::ecc::{scalar_mul::fixed_base::scalar_mul, Point};
use dusk_plonk::prelude::*;
use dusk_poseidon::{
    sponge,
    tree::{merkle_opening as merkle_opening_gadget, PoseidonBranch},
};
use plonk_gadgets::{AllocatedScalar, RangeGadgets::max_bound};

/// common constraints
///
/// bid constraints:
///   1. (t_p>=m_p) * (m_a*(t_a>=m_a)+(t_a<m_a)*t_a) == amount
///   2. (t_p>=m_p) * m_p == price
///   3. (t_a-amount), t_p, (m_a-amount), m_p  --> merkle_tree
#[derive(Debug, Clone)]
pub struct MatcherCircuit<'a> {
    // TODO merkle_tree
    ma: BlsScalar,
    mp: BlsScalar,
    ta: BlsScalar,
    tp: BlsScalar,
}

impl<'a> Circuit<'a> for MatcherCircuit<'a> {
    fn gadget(&mut self, composer: &mut StandardComposer) -> Result<()> {
        // bid test
        let ma = composer.add_input(self.ma);
        let mp = composer.add_input(self.mp);
        let ta = composer.add_input(self.ta);
        let tp = composer.add_input(self.tp);

        // ---------calculate bid-1 constraint-----------
        // ----------------------------------------------

        // ------------bid-constraint-1-q-p--------------
        // t_p>=m_p <=> m_p-t_p<=0 <=> m_p-t_p>2^64
        let cg_scalar = mp.scalar - tp.scalar;
        let cg_var = composer.add(
            (BlsScalar::one(), mp.var),
            (-BlsScalar::one(), tp.var),
            BlsScalar::zero(),
            BlsScalar::zero(),
        );
        let cgv = AllocatedScalar {
            scalar: cg_scalar,
            var: cg_var,
        };
        let bc_1_q_p = max_bound(composer, BlsScalar::from(2u64).pow(&[64, 0, 0, 0]), cgv).0;
        // ----------bid-constraint-1-ta-or-ma------------
        // t_a>=m_a <=> m_a-t_a<=0 <=> m_a-t_a>2^64
        let _left_scalar = ma.scalar - ta.scalar;
        let _left_var = composer.add(
            (BlsScalar::one(), ma.var),
            (-BlsScalar::one(), ta.var),
            BlsScalar::zero(),
            BlsScalar::zero(),
        );
        let _lqv = AllocatedScalar {
            scalar: _left_scalar,
            var: _left_var,
        };
        let _lq = max_bound(composer, BlsScalar::from(2u64).pow(&[64, 0, 0, 0]), _lqv).0;
    }
}
