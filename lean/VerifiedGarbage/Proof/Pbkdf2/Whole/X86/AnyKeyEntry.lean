module

import VerifiedGarbage.Proof.Framework.EntryBranch
public import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.AnyKeyCT
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Frame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Md5.X86.Lit
import VerifiedGarbage.Proof.Sha512.X86.Lit

/-!
# HMAC's `init` for a key of any length on x86 (32-bit), choosing on entry

`initEntry B short long` loads `key_len` (argument 3) into `eax`, compares it
with `B + 1` and runs `long`, verified against
`VG.Spec.Hmac.Instance.initAnyKeyContract`, for a key longer than a block,
and `short`, verified against `initContract` (a key of at most a block),
otherwise (`Verified.entryBranch`). The comparison writes only `eax` and the
flags, which no contract reads, and leaks only the address of the argument;
the branch depends only on `key_len`, which is public.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Whole.X86

open VG.X86

theorem entry_run {B : Nat} (hB : B + 1 < 2 ^ 32) (s : State)
    (hin : InRegions (s.rd ++ s.wr) (argAddr s 3) 4) :
    ∃ u, execBlock isa [.mov .eax (Impl.Pbkdf2.Whole.X86.Fns.argM 3),
        .alu .cmp .eax (.imm (BitVec.ofNat 32 (B + 1)))] s = some (u, [.addr (argAddr s 3)]) ∧
      (∀ r, r ≠ .eax → u.gpr r = s.gpr r) ∧ u.mem = s.mem ∧ u.rd = s.rd ∧ u.wr = s.wr ∧
      eval .ae u = some (decide (B + 1 ≤ (arg s 3).toNat)) := by
  have ea : s.ea (VG.Impl.Pbkdf2.Stream.X86.at_ .esp (4 + 4 * 3)) = argAddr s 3 := rfl
  have he : exec (.mov .eax (Impl.Pbkdf2.Whole.X86.Fns.argM 3)) s = some (s.setReg .eax (arg s 3)) := by
    simp [exec, readSrc, State.load32, Impl.Pbkdf2.Whole.X86.Fns.argM, ea, hin, arg]
  obtain ⟨u, hu⟩ : ∃ u, exec (.alu .cmp .eax (.imm (BitVec.ofNat 32 (B + 1)))) (s.setReg .eax (arg s 3)) =
      some u := ⟨_, rfl⟩
  obtain ⟨t, u', e, f, c⟩ := VG.Proof.Sha256.X86.Stream.wp_cmpi (s := s.setReg .eax (arg s 3)) (is := [])
    (Q := fun u => VG.Proof.Sha256.X86.Stream.Fupd (s.setReg .eax (arg s 3)) u ∧
      u.cf = some (decide ((arg s 3).toNat < (BitVec.ofNat 32 (B + 1)).toNat)))
    (d := .eax) (v := BitVec.ofNat 32 (B + 1)) (fun s' f c _ => WP.block_nil ⟨f, by rw [c]; rfl⟩)
  have x := Exec.block_eq (T := X86.target) e
  simp only [execBlock, hu] at x
  obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj x)
  refine ⟨u, ?_, fun r hr => ?_, by rw [f.mem]; rfl, by rw [f.rd]; rfl, by rw [f.wr]; rfl, ?_⟩
  · simp only [execBlock, he, hu]; rfl
  · rw [f.gpr]; show (s.setReg .eax (arg s 3)).gpr r = s.gpr r
    simp [State.setReg, hr]
  · show Option.map (!·) u.cf = _
    rw [c, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hB]
    simp only [Option.map_some, ← decide_not, Nat.not_lt]

theorem argAddr_congr {u s : State} (h : u.gpr .esp = s.gpr .esp) (i : Nat) : argAddr u i = argAddr s i := by
  show (u.gpr .esp + _).setWidth 64 = (s.gpr .esp + _).setWidth 64; rw [h]

theorem argVal_congr {u s : State} (h : u.gpr .esp = s.gpr .esp) (hm : u.mem = s.mem) (i : Nat) :
    argVal u 32 i = argVal s 32 i := by
  rw [argVal32, argVal32]
  show (u.mem.readW (argAddr u i) 32).setWidth 64 = (s.mem.readW (argAddr s i) 32).setWidth 64
  rw [argAddr_congr h, hm]

theorem initEntry_verified {I : Spec.Hmac.Instance} {short long : Prog isa} {n₁ n₂ : Nat}
    (hS : Verified X86.target short (I.initContract X86.abi n₁))
    (hL : Verified X86.target long (I.initAnyKeyContract X86.abi n₂))
    (h₁ : 0 < n₁) (hn : n₁ ≤ n₂) (hB : I.S.H.blockSize + 1 < 2 ^ 32)
    (hsat : ∃ s, (I.initAnyKeyContract X86.abi n₂).pre s) :
    Verified X86.target (Impl.Pbkdf2.Whole.X86.initEntry I.S.H.blockSize short long)
      (I.initAnyKeyContract X86.abi n₂) := by
  have hcs : ∀ r ∈ calleeSaved, r ≠ .eax := by decide
  have run : ∀ s, (I.initAnyKeyContract X86.abi n₂).pre s → ∃ u,
      execBlock isa [.mov .eax (Impl.Pbkdf2.Whole.X86.Fns.argM 3),
        .alu .cmp .eax (.imm (BitVec.ofNat 32 (I.S.H.blockSize + 1)))] s = some (u, [.addr (argAddr s 3)]) ∧
      (∀ r, r ≠ .eax → u.gpr r = s.gpr r) ∧ u.mem = s.mem ∧ u.rd = s.rd ∧ u.wr = s.wr ∧
      eval .ae u = some (decide (I.S.H.blockSize + 1 ≤ (arg s 3).toNat)) := fun s hs => by
    refine entry_run hB s ?_
    sig_pre [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig,
      Spec.Hmac.initPost, X86.abi] at hs
    obtain ⟨h0, -, h2, -⟩ := hs
    have hf : (s.gpr .esp).toNat + 4 + 16 ≤ 2 ^ 32 := by
      revert h0; cases n₂ <;> simp [argBytes] <;> omega_arith
    have hr : (⟨addr (s.gpr .esp) 4, 16⟩ : Region) = ⟨argAddr s 0, argBytes [32, 32, 32, 32]⟩ := rfl
    refine ⟨_, ?_, Pbkdf2.Stream.X86.arg_contains rfl (by omega_arith) hf⟩
    rw [h2, hr]
    exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  refine Verified.entryBranch (p := fun s => decide (I.S.H.blockSize + 1 ≤ (arg s 3).toNat))
    (fun s => [.addr (argAddr s 3)]) hL hS (fun s hs => ?_) ?_ hsat
  · obtain ⟨u, e, g, hm, hrd, hwr, ev⟩ := run s hs
    have hesp : u.gpr .esp = s.gpr .esp := g .esp (by decide)
    have haddr : ∀ i, argAddr u i = argAddr s i := argAddr_congr hesp
    have hval : ∀ i, argVal u 32 i = argVal s 32 i := argVal_congr hesp hm
    have abi : ∀ s', X86.target.abiPreserved u s' → X86.target.abiPreserved s s' := fun s' a =>
      ⟨fun x hx => by rw [a.1 x hx, g x (hcs x hx)], by rw [← hesp, a.2, hm]⟩
    refine ⟨u, e, ev, fun _ => ⟨?_, fun s' a q => ⟨abi s' a, ?_⟩⟩, fun hp => ⟨?_, fun s' a q => ⟨abi s' a, ?_⟩⟩⟩
    · sig_pre [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig,
        Spec.Hmac.initPost, X86.abi] at hs ⊢
      simp only [hval, haddr, hesp, hrd, hwr]
      exact hs
    · sig_post [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig,
        Spec.Hmac.initPost, X86.abi] at q ⊢
      simp only [hval, hm] at q
      exact q
    · have hk : (arg s 3).toNat ≤ I.S.H.blockSize := by have := of_decide_eq_false hp; omega_arith
      sig_pre [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig,
        Spec.Hmac.initPost, X86.abi] at hs
      sig_pre [Spec.Hmac.Instance.initContract, Spec.Hmac.initContract, Spec.Hmac.initSig, Spec.Hmac.initPre,
        Spec.Hmac.initPost, X86.abi]
      obtain ⟨m₁, rfl⟩ : ∃ m, n₁ = m + 1 := ⟨n₁ - 1, by omega_arith⟩
      obtain ⟨m₂, rfl⟩ : ∃ m, n₂ = m + 1 := ⟨n₂ - 1, by omega_arith⟩
      simp only [hval, haddr, hesp, hrd, hwr]
      simp only [Sig.conj, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
        List.append_nil] at hs ⊢
      obtain ⟨⟨h0, h0'⟩, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, ⟨c0, c1, c2, c3, c4⟩, n1, n2, n3⟩ := hs
      have sb := Offset.sub_below ((s.gpr .esp).setWidth 64) (a := m₁ + 1) (n := m₁ + 1) (b := m₂ + 1)
        (m := m₂ + 1) (by omega_arith) (by omega_arith)
      refine ⟨⟨by omega_arith, h0'⟩, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
        ⟨c0, c1.sub_left sb, c2.sub_left sb, c3.sub_left sb, c4.sub_left sb⟩, n1, n2, n3, ?_⟩
      rw [argVal32, setWidth32_64]; exact hk
    · sig_post [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig,
        Spec.Hmac.initPost, X86.abi]
      sig_post [Spec.Hmac.Instance.initContract, Spec.Hmac.initContract, Spec.Hmac.initSig, Spec.Hmac.initPre,
        Spec.Hmac.initPost, X86.abi] at q
      simp only [hval, hm] at q
      exact q
  · intro s s' u u' hs hs' hq e e'
    obtain ⟨u₀, e₀, g, hm, -, -, -⟩ := run s hs
    obtain ⟨u₀', e₀', g', hm', -, -, -⟩ := run s' hs'
    rw [e₀] at e; rw [e₀'] at e'
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj e)
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj e')
    have hesp := g .esp (by decide)
    have hesp' := g' .esp (by decide)
    have hq' := hq
    sig_pub [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig,
      Spec.Hmac.initPost, X86.abi] at hq'
    obtain ⟨q0, q1, q2, q3, q4⟩ := hq'
    have e3 : arg s 3 = arg s' 3 := by rwa [argVal32, argVal32, setWidth32_64, setWidth32_64] at q4
    have pu : (I.initAnyKeyContract X86.abi n₂).pub u₀ u₀' := by
      sig_pub [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig,
        Spec.Hmac.initPost, X86.abi]
      simp only [argVal_congr hesp hm, argVal_congr hesp' hm', hesp, hesp']
      exact ⟨q0, q1, q2, q3, q4⟩
    refine ⟨by rw [argAddr_congr q0], by rw [e3], fun _ => pu, fun _ => pu⟩

/-- HMAC's `init` for a key of any length, `vg_hmac_<hash>_init`, of instance
`I`: for a key of at most a block, `init_scratch` (`hmacInit`) in a frame
holding its working space; for a longer key (cold), `F.hmacInitAny`, in a
frame holding its larger working space, which it wipes. -/
def initCode (I : Spec.Hmac.Instance) (hmacInit : Prog isa) (F : Impl.Pbkdf2.Whole.X86.Fns) : Prog isa :=
  Impl.Pbkdf2.Whole.X86.initEntry I.S.H.blockSize
    (Impl.StackScratch.X86.withStackScratch (Md.X86.initFrame I) 4 hmacInit)
    (Impl.StackScratch.X86.withStackScratchWiped (Any.anyFrame I) 4 (2 * I.initAnyKeyScratch) F.hmacInitAny)

theorem initCode_verified {I : Spec.Hmac.Instance} {c : Prog isa} {F : Impl.Pbkdf2.Whole.X86.Fns}
    (hS : Verified X86.target (Impl.StackScratch.X86.withStackScratch (Md.X86.initFrame I) 4 c)
      (I.initContract X86.abi (48 + Md.X86.initFrame I)))
    (hL : Verified X86.target
      (Impl.StackScratch.X86.withStackScratchWiped (Any.anyFrame I) 4 (2 * I.initAnyKeyScratch) F.hmacInitAny)
      (I.initAnyKeyContract X86.abi (76 + Any.anyFrame I)))
    (hB : I.S.H.blockSize + 1 < 2 ^ 32)
    (hsat : ∃ s, (I.initAnyKeyContract X86.abi (76 + Any.anyFrame I)).pre s) :
    Verified X86.target (initCode I c F) (I.initAnyKeyContract X86.abi (76 + Any.anyFrame I)) :=
  initEntry_verified hS hL (by omega_arith)
    (by simp only [Md.X86.initFrame, Any.anyFrame, Spec.Hmac.Instance.initAnyKeyScratch]; omega_arith) hB hsat

theorem initCode_spSafe {I : Spec.Hmac.Instance} {c : Prog isa} {F : Impl.Pbkdf2.Whole.X86.Fns}
    (hs : c.all (fun i => !isa.writesSp i) = true)
    (hf : (Impl.StackScratch.X86.withStackScratch (Md.X86.initFrame I) 4 (.block [])).all
      (fun i => !isa.writesSp i) = true)
    (hl : (Impl.StackScratch.X86.withStackScratchWiped (Any.anyFrame I) 4 (2 * I.initAnyKeyScratch)
      F.hmacInitAny).all (fun i => !isa.writesSp i) = true) :
    (initCode I c F).all (fun i => !isa.writesSp i) = true := by
  have hs' := Md.X86.withStackScratch_spSafe (bytes := Md.X86.initFrame I) (n := 4) hs hf
  simp only [initCode, Impl.Pbkdf2.Whole.X86.initEntry, Code.iteCold, Code.all, hs', hl, Bool.and_true]
  rfl

end VG.Proof.Pbkdf2.Whole.X86
