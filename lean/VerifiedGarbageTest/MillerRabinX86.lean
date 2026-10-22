import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.Proof.MillerRabin.X86.Verified
import VerifiedGarbage.Proof.Dsa.X86.Generation.QShape
import VerifiedGarbage.Proof.Dsa.X86.Generation.QShapeTiming
import VerifiedGarbage.Proof.Dsa.X86.Generation.Hashes

import VerifiedGarbage.Proof.Dsa.X86.Generation.SeedAdd
import VerifiedGarbage.Proof.Dsa.X86.Generation.SeedAddTiming
import VerifiedGarbage.Proof.Dsa.X86.Generation.Reduce
import VerifiedGarbage.Proof.Dsa.X86.Generation.Header
import VerifiedGarbage.Proof.Mont.X86.Inverse64
import VerifiedGarbage.Proof.Dsa.X86.Generation.TrialInverse
import VerifiedGarbage.Proof.Dsa.X86.Generation.TrialScan
import VerifiedGarbage.Proof.Dsa.X86.Generation.TrialFlag
import VerifiedGarbage.Proof.Dsa.X86.Generation.TrialTest
import VerifiedGarbage.Proof.Dsa.X86.Generation.TrialPrime
import VerifiedGarbage.Proof.Dsa.X86.Generation.TrialTable
import VerifiedGarbage.Proof.Dsa.X86.Generation.TrialLoop
import VerifiedGarbage.Proof.Dsa.X86.Generation.TrialLoopTiming
import VerifiedGarbage.Proof.Dsa.X86.Generation.Halving
import VerifiedGarbage.Proof.Dsa.X86.Generation.HalvingTiming
import VerifiedGarbage.Proof.Dsa.X86.Generation.PreparedExponent
import VerifiedGarbage.Proof.Dsa.X86.Generation.ExponentTiming
import VerifiedGarbage.Proof.Dsa.X86.Generation.CompactHeader
import VerifiedGarbage.Proof.Dsa.X86.Generation.CompactInverseLayout
import VerifiedGarbage.Proof.Dsa.X86.Generation.CompactTiming
import VerifiedGarbage.Proof.Dsa.X86.Generation.CandidateExponent
import VerifiedGarbage.Proof.Dsa.X86.Generation.CandidateExponentTiming
import VerifiedGarbage.Proof.Dsa.X86.Generation.MontgomerySetupTiming
import VerifiedGarbage.Proof.Dsa.X86.Generation.MontgomeryConstants
import VerifiedGarbage.Proof.Dsa.X86.Generation.TransferValues
import VerifiedGarbage.Proof.Dsa.X86.Generation.TransferTiming
import VerifiedGarbage.Impl.Dsa.X86.Generation.PrimePreparation
import VerifiedGarbage.Proof.Dsa.X86.Generation.CompactTransferLayout
import VerifiedGarbage.Proof.Dsa.X86.Generation.ArithmeticFrame
import VerifiedGarbage.Proof.Dsa.X86.Generation.CandidateTransfer
import VerifiedGarbage.Proof.Dsa.X86.Generation.FactorAt
import VerifiedGarbage.Proof.Dsa.X86.Generation.HeaderAt
import VerifiedGarbage.Proof.Dsa.X86.Generation.FinalizeCandidate
import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimePreparation
import VerifiedGarbage.Proof.Dsa.X86.Generation.WitnessRange
import VerifiedGarbage.Proof.Dsa.X86.Generation.EncodeWitness
import VerifiedGarbage.Proof.Dsa.X86.Generation.LoadWitness
import VerifiedGarbage.Proof.Dsa.X86.Generation.ForceWitness

import VerifiedGarbage.Proof.Dsa.X86.Generation.SamplePrepared
import VerifiedGarbage.Proof.Dsa.X86.Generation.WitnessPrepared

import VerifiedGarbage.Proof.Dsa.X86.Generation.RoundCall
import VerifiedGarbage.Proof.MillerRabin.ReusableKeeps

import VerifiedGarbage.Proof.Dsa.X86.Generation.SampleRound
import VerifiedGarbage.Proof.Dsa.X86.Generation.RoundTail

import VerifiedGarbage.Proof.Dsa.X86.Generation.TestedDraw
import VerifiedGarbage.Proof.Dsa.X86.Generation.TapeCheck
import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeLoopInit
import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeLoopEnd

import VerifiedGarbage.Proof.Dsa.X86.Generation.MillerRabin

import VerifiedGarbage.Proof.Dsa.X86.Generation.ProbablePrime
import VerifiedGarbage.Proof.Dsa.X86.Generation.QCandidate
import VerifiedGarbage.Proof.Dsa.X86.Generation.CheckCandidate
import VerifiedGarbage.Proof.Dsa.X86.Generation.Subgroup
import VerifiedGarbage.Proof.Dsa.X86.Generation.PHashes
import VerifiedGarbage.Proof.Dsa.X86.Generation.PShape
import VerifiedGarbage.Proof.Dsa.X86.Generation.PConstruct

#assert_standard_axioms VG.Proof.MillerRabin.X86.round_verified
#assert_standard_axioms VG.Proof.Dsa.X86.Generation.q_shape
#assert_standard_axioms VG.Proof.Dsa.X86.Generation.q_shape_ct
#assert_standard_axioms VG.Proof.Dsa.X86.Generation.seed_hash
#assert_standard_axioms VG.Proof.Dsa.X86.Generation.seed_hash_ct

#assert_standard_axioms VG.Proof.Dsa.X86.Generation.seed_add
#assert_standard_axioms VG.Proof.Dsa.X86.Generation.seed_add_ct
#assert_standard_axioms VG.Proof.Dsa.X86.Generation.reduce_candidate
#assert_standard_axioms VG.Proof.Dsa.X86.Generation.set_header
#assert_standard_axioms VG.Proof.Mont.X86.extend_inverse
#assert_standard_axioms VG.Proof.Dsa.X86.Generation.trial_reduce
#assert_standard_axioms VG.Proof.Dsa.X86.Generation.trial_inverse
#assert_standard_axioms VG.Proof.Dsa.X86.Generation.trial_scan
#assert_standard_axioms VG.Proof.Dsa.X86.Generation.trial_flag
#assert_standard_axioms VG.Proof.Dsa.X86.Generation.trial_test
#assert_standard_axioms VG.Proof.Dsa.X86.Generation.trial_prime
#assert_standard_axioms VG.Proof.Dsa.X86.Generation.trial_table
#assert_standard_axioms VG.Proof.Dsa.X86.Generation.trial_loop_dsa
#assert_standard_axioms VG.Proof.Dsa.X86.Generation.trial_loop_ct
#assert_standard_axioms VG.Proof.Dsa.X86.Generation.halving
#assert_standard_axioms VG.Proof.Dsa.X86.Generation.halving_ct
#assert_standard_axioms VG.Proof.Dsa.X86.Generation.exponent_setup
#assert_standard_axioms VG.Proof.Dsa.X86.Generation.prepare_exponent_ct

#assert_standard_axioms VG.Proof.Dsa.X86.Generation.prepare_exponent
#assert_standard_axioms VG.Proof.Bignum.X86.TwoPower.code_ok
#assert_standard_axioms VG.Proof.Dsa.X86.Generation.compact_header
#assert_standard_axioms VG.Proof.Dsa.X86.Generation.compact_header_ct
#assert_standard_axioms VG.Proof.Dsa.X86.Generation.compact_inverse_layout
#assert_standard_axioms VG.Proof.Dsa.X86.Generation.compact_inverse_ct
#assert_standard_axioms VG.Proof.Dsa.X86.Generation.prepare_candidate_exponent
#assert_standard_axioms VG.Proof.Dsa.X86.Generation.prepare_candidate_exponent_ct
#assert_standard_axioms VG.Proof.Dsa.X86.Generation.montgomery_ok
#assert_standard_axioms VG.Proof.Dsa.X86.Generation.montgomery_ct
#assert_standard_axioms VG.Proof.Dsa.X86.Generation.montgomery_setup
#assert_standard_axioms VG.Proof.Dsa.X86.Generation.montgomery_setup_ct
#assert_standard_axioms VG.Proof.Dsa.X86.Generation.montgomery_constants
#assert_standard_axioms VG.Proof.Dsa.X86.Generation.save_exponent
#assert_standard_axioms VG.Proof.Dsa.X86.Generation.compact_numbers
#assert_standard_axioms VG.Proof.Dsa.X86.Generation.transfer_words_ct
#assert_standard_axioms VG.Proof.Dsa.X86.Generation.compact_numbers_shared
#assert_standard_axioms VG.Proof.Dsa.X86.Generation.compact_transfer_layout
#assert_standard_axioms VG.Proof.Dsa.X86.Generation.with_arithmetic
#assert_standard_axioms VG.Proof.Dsa.X86.Generation.arithmetic_ready
#assert_standard_axioms VG.Proof.Dsa.X86.Generation.parent_constants
#assert_standard_axioms VG.Proof.Dsa.X86.Generation.candidate_transfer
#assert_standard_axioms VG.Proof.Dsa.X86.Generation.factor_at
#assert_standard_axioms VG.Proof.Dsa.X86.Generation.header_at
#assert_standard_axioms VG.Proof.Dsa.X86.Generation.finalize_candidate
#assert_standard_axioms VG.Proof.Dsa.X86.Generation.prime_preparation
#assert_standard_axioms VG.Proof.Dsa.X86.Generation.witness_init
#assert_standard_axioms VG.Proof.Dsa.X86.Generation.witness_range
#assert_standard_axioms VG.Proof.Dsa.X86.Generation.encode_witness
#assert_standard_axioms VG.Proof.Dsa.X86.Generation.load_witness
#assert_standard_axioms VG.Proof.Dsa.X86.Generation.force_witness_spec

#assert_standard_axioms VG.Proof.Dsa.X86.Generation.sample_witness
#assert_standard_axioms VG.Proof.Dsa.X86.Generation.sample_prepared
#assert_standard_axioms VG.Proof.Dsa.X86.Generation.witness_prepared

#assert_standard_axioms VG.Proof.Dsa.X86.Generation.round_call
#assert_standard_axioms VG.Proof.MillerRabin.PreparedCore.kept
#assert_standard_axioms VG.Proof.Dsa.X86.Generation.witness_core
#assert_standard_axioms VG.Proof.Dsa.X86.Generation.sample_core

#assert_standard_axioms VG.Proof.Dsa.X86.Generation.sample_round
#assert_standard_axioms VG.Proof.Dsa.X86.Generation.round_tail

#assert_standard_axioms VG.Proof.Dsa.X86.Generation.draw_copy
#assert_standard_axioms VG.Proof.Dsa.X86.Generation.draw_from_tape
#assert_standard_axioms VG.Proof.Dsa.X86.Generation.draw_round
#assert_standard_axioms VG.Proof.Dsa.X86.Generation.tested_draw
#assert_standard_axioms VG.Proof.Dsa.X86.Generation.tape_check
#assert_standard_axioms VG.Proof.Dsa.X86.Generation.prime_loop_init
#assert_standard_axioms VG.Proof.Dsa.X86.Generation.prime_loop_end

#assert_standard_axioms VG.Proof.Dsa.X86.Generation.witness_loop
#assert_standard_axioms VG.Proof.Dsa.X86.Generation.miller_rabin

#assert_standard_axioms VG.Proof.Dsa.X86.Generation.trial_loop_early_dsa
#assert_standard_axioms VG.Proof.Dsa.X86.Generation.candidate_trial
#assert_standard_axioms VG.Proof.Dsa.X86.Generation.test_candidate
#assert_standard_axioms VG.Proof.Dsa.X86.Generation.probable_prime

#assert_standard_axioms VG.Proof.Dsa.X86.Generation.q_candidate
#assert_standard_axioms VG.Proof.Dsa.X86.Generation.check_candidate
#assert_standard_axioms VG.Proof.Dsa.X86.Generation.subgroup_arguments

#assert_standard_axioms VG.Proof.Dsa.X86.Generation.subgroup_candidate

#assert_standard_axioms VG.Proof.Dsa.X86.Generation.hash_workspace
#assert_standard_axioms VG.Proof.Dsa.X86.Generation.subgroup_hash
#assert_standard_axioms VG.Proof.Dsa.X86.Generation.subgroup_ok

#assert_standard_axioms VG.Proof.Dsa.X86.Generation.hash_digest_workspace
#assert_standard_axioms VG.Proof.Dsa.X86.Generation.p_seed
#assert_standard_axioms VG.Proof.Dsa.X86.Generation.p_hash_one
#assert_standard_axioms VG.Proof.Dsa.X86.Generation.p_hashes

#assert_standard_axioms VG.Proof.Dsa.X86.Generation.shape_workspace
#assert_standard_axioms VG.Proof.Dsa.X86.Generation.p_shape

#assert_standard_axioms VG.Proof.Dsa.X86.Generation.prepared_reduction
#assert_standard_axioms VG.Proof.Dsa.X86.Generation.reduce_at
#assert_standard_axioms VG.Proof.Dsa.X86.Generation.stage_reduction
#assert_standard_axioms VG.Proof.Dsa.X86.Generation.save_reduction
#assert_standard_axioms VG.Proof.Dsa.X86.Generation.p_reduce
#assert_standard_axioms VG.Proof.Dsa.X86.Generation.p_construct
