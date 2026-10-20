module

import VerifiedGarbage.Proof.Framework.EntryBranch
public import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.AnyKeyCT
public import VerifiedGarbage.Proof.Pbkdf2.Md.Arm.Frame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Arm.Contract

/-!
# HMAC's `init` for a key of any length on 32-bit ARM, choosing on entry

`initEntry B short long` sets `Z` to whether `key_len` (`r3`) is at most `B`
(through `r12`, as `pbkdf2`'s `cmpPw`) and runs `long`, verified against
`VG.Spec.Hmac.Instance.initAnyKeyContract`, for a key longer than a block,
and `short`, verified against `initContract` (a key of at most a block),
otherwise (`Verified.entryBranch`). The comparison writes only `r12` and the
flags, which no contract reads, and leaks nothing; the branch depends only
on `key_len`, which is public.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Whole.Arm

open VG.Arm

/-- The comparison on entry. -/
abbrev entryB (B : Nat) : List Instr :=
  [.subs .r12 .r3 (.imm (BitVec.ofNat 32 (B + 1))), .mov .r12 (.imm 0), .adc .r12 .r12 (.imm 0),
    .cmp .r12 (.imm 0)]

theorem entry_run {B : Nat} (hB : B + 1 < 2 ^ 32) (hk : encodable (BitVec.ofNat 32 (B + 1)) = true) (s : State) :
    ∃ u, execBlock isa (entryB B) s = some (u, []) ∧ (∀ r, r ≠ .r12 → u.gpr r = s.gpr r) ∧ u.mem = s.mem ∧
      u.rd = s.rd ∧ u.wr = s.wr ∧ u.sp = s.sp ∧ eval .ne u = some (decide (B + 1 ≤ (s.gpr .r3).toNat)) := by
  obtain ⟨t, u, e, g, m, rd, wr, sp, z⟩ := wp_lt (s := s) (is := []) (x := .r3) (Q := fun u =>
      (∀ r, r ≠ .r12 → u.gpr r = s.gpr r) ∧ u.mem = s.mem ∧ u.rd = s.rd ∧ u.wr = s.wr ∧ u.sp = s.sp ∧
        u.z = decide ((s.gpr .r3).toNat < (BitVec.ofNat 32 (B + 1)).toNat)) hk
    fun s' g m rd wr sp z => WP.block_nil ⟨g, m, rd, wr, sp, z⟩
  have x := Exec.block_eq (T := Arm.target) e
  have ht := execBlock_trace_nil (M := isa) (b := entryB B) (fun i hi s => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> rfl) x
  subst ht
  refine ⟨u, x, g, m, rd, wr, sp, ?_⟩
  show some (!u.z) = _
  rw [z, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hB]
  simp only [← decide_not, Nat.not_lt]

theorem initEntry_verified {I : Spec.Hmac.Instance} {short long : Prog isa} {n₁ n₂ : Nat}
    (hS : Verified Arm.target short (I.initContract Arm.abi n₁))
    (hL : Verified Arm.target long (I.initAnyKeyContract Arm.abi n₂))
    (h₁ : 0 < n₁) (hn : n₁ ≤ n₂) (hB : I.S.H.blockSize + 1 < 2 ^ 32)
    (hk : encodable (BitVec.ofNat 32 (I.S.H.blockSize + 1)) = true)
    (hsat : ∃ s, (I.initAnyKeyContract Arm.abi n₂).pre s) :
    Verified Arm.target (Impl.Pbkdf2.Whole.Arm.initEntry I.S.H.blockSize short long)
      (I.initAnyKeyContract Arm.abi n₂) := by
  have hp : ∀ r ∈ preserved, r ≠ .r12 := by decide
  refine Verified.entryBranch (p := fun s => decide (I.S.H.blockSize + 1 ≤ (s.gpr .r3).toNat))
    (fun _ => []) hL hS (fun s hs => ?_) ?_ hsat
  · obtain ⟨u, e, g, hm, hrd, hwr, hsp, ev⟩ := entry_run hB hk s
    have g0 := g .r0 (by decide)
    have g1 := g .r1 (by decide)
    have g2 := g .r2 (by decide)
    have g3 := g .r3 (by decide)
    have abi : ∀ s', Arm.target.abiPreserved u s' → Arm.target.abiPreserved s s' := fun s' a =>
      ⟨fun x hx => by rw [a.1 x hx, g x (hp x hx)], by rw [a.2, hsp]⟩
    refine ⟨u, e, ev, fun _ => ⟨?_, fun s' a q => ⟨abi s' a, ?_⟩⟩, fun hp => ⟨?_, fun s' a q => ⟨abi s' a, ?_⟩⟩⟩
    · sig_pre [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig,
        Spec.Hmac.initPost, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hs ⊢
      rw [g0, g1, g2, g3, hsp, hrd, hwr]; exact hs
    · sig_post [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig,
        Spec.Hmac.initPost, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at q ⊢
      rw [g0, g1, g2, g3, hm] at q; exact q
    · have hk : (s.gpr .r3).toNat ≤ I.S.H.blockSize := by have := of_decide_eq_false hp; omega
      sig_pre [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig,
        Spec.Hmac.initPost, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hs
      sig_pre [Spec.Hmac.Instance.initContract, Spec.Hmac.initContract, Spec.Hmac.initSig, Spec.Hmac.initPre,
        Spec.Hmac.initPost, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
      rw [g0, g1, g2, g3, hsp, hrd, hwr]
      obtain ⟨m₁, rfl⟩ : ∃ m, n₁ = m + 1 := ⟨n₁ - 1, by omega⟩
      obtain ⟨m₂, rfl⟩ : ∃ m, n₂ = m + 1 := ⟨n₂ - 1, by omega⟩
      simp only [Sig.conj, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
        List.append_nil] at hs ⊢
      obtain ⟨⟨h0, h0'⟩, h1, h2, h3, h4, h5, ⟨c1, c2, c3⟩, n1, n2, n3⟩ := hs
      have sb := Offset.sub_below (State.addr s.sp) (a := m₁ + 1) (n := m₁ + 1) (b := m₂ + 1) (m := m₂ + 1)
        (by omega) (by omega)
      exact ⟨⟨by omega, h0'⟩, h1, h2, h3, h4, h5, ⟨c1.sub_left sb, c2.sub_left sb, c3.sub_left sb⟩, n1, n2, n3, hk⟩
    · sig_post [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig,
        Spec.Hmac.initPost, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
      sig_post [Spec.Hmac.Instance.initContract, Spec.Hmac.initContract, Spec.Hmac.initSig, Spec.Hmac.initPre,
        Spec.Hmac.initPost, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at q
      rw [g0, g1, g2, g3, hm] at q; exact q
  · intro s s' u u' hs hs' hq e e'
    obtain ⟨u₀, e₀, g, -, -, -, hsp, -⟩ := entry_run hB hk s
    obtain ⟨u₀', e₀', g', -, -, -, hsp', -⟩ := entry_run hB hk s'
    rw [e₀] at e; rw [e₀'] at e'
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj e)
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj e')
    have hq' := hq
    sig_pub [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig,
      Spec.Hmac.initPost, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hq'
    obtain ⟨q0, q1, q2, q3, q4⟩ := hq'
    have pu : (I.initAnyKeyContract Arm.abi n₂).pub u₀ u₀' := by
      sig_pub [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig,
        Spec.Hmac.initPost, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
      rw [hsp, hsp', g .r0 (by decide), g' .r0 (by decide), g .r1 (by decide), g' .r1 (by decide),
        g .r2 (by decide), g' .r2 (by decide), g .r3 (by decide), g' .r3 (by decide)]
      exact ⟨q0, q1, q2, q3, q4⟩
    exact ⟨rfl, by rw [q4], fun _ => pu, fun _ => pu⟩

/-- HMAC's `init` for a key of any length, `vg_hmac_<hash>_init`, of instance
`I`: for a key of at most a block, `init_scratch` (`hmacInit`) in a frame
holding its working space; for a longer key (cold), `F.hmacInitAny`, in a
frame holding its larger working space, which it wipes. -/
def initCode (I : Spec.Hmac.Instance) (hmacInit : Prog isa) (F : Impl.Pbkdf2.Whole.Arm.Fns) : Prog isa :=
  Impl.Pbkdf2.Whole.Arm.initEntry I.S.H.blockSize
    (Impl.StackScratch.Arm.withStackScratch (Md.Arm.frame I) 0 hmacInit)
    (Impl.StackScratch.Arm.withStackScratchWiped (Any.anyFrame I) 0 (2 * I.initAnyKeyScratch) F.hmacInitAny)

theorem initCode_verified {I : Spec.Hmac.Instance} {c : Prog isa} {F : Impl.Pbkdf2.Whole.Arm.Fns}
    (hS : Verified Arm.target (Impl.StackScratch.Arm.withStackScratch (Md.Arm.frame I) 0 c)
      (I.initContract Arm.abi (16 + Md.Arm.frame I)))
    (hL : Verified Arm.target
      (Impl.StackScratch.Arm.withStackScratchWiped (Any.anyFrame I) 0 (2 * I.initAnyKeyScratch) F.hmacInitAny)
      (I.initAnyKeyContract Arm.abi (24 + Any.anyFrame I)))
    (hn : 16 + Md.Arm.frame I ≤ 24 + Any.anyFrame I) (hB : I.S.H.blockSize + 1 < 2 ^ 32)
    (hk : encodable (BitVec.ofNat 32 (I.S.H.blockSize + 1)) = true)
    (hsat : ∃ s, (I.initAnyKeyContract Arm.abi (24 + Any.anyFrame I)).pre s) :
    Verified Arm.target (initCode I c F) (I.initAnyKeyContract Arm.abi (24 + Any.anyFrame I)) :=
  initEntry_verified hS hL (by omega) hn hB hk hsat

end VG.Proof.Pbkdf2.Whole.Arm
