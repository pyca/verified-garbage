module

-- separate module: the top level's constant-time proof, kept apart from the kernel's evaluation of the code's facts

public import VerifiedGarbage.Proof.SlhDsa.X86_64.VerifyTopCTBody
public import VerifiedGarbage.Proof.SlhDsa.X86_64.VerifyTopTop
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsCT
import VerifiedGarbage.Proof.SlhDsa.X86_64.VerifyTopIdx
import VerifiedGarbage.Proof.SlhDsa.X86_64.KeyGen
import VerifiedGarbage.Proof.SlhDsa.X86_64.ForsLeaf

/-!
# SLH-DSA (SHAKE) on x86-64, `verify`: constant time

Untrusted: everything here is checked by Lean. Two runs of `verify` whose
public data agree (the pointers, the lengths, and the bytes of the public
key, the message, the context string and the signature: `verifyContract`'s
`pub`) have the same layout and the same inputs (`Inp`), so their tests of
`ctx_len` and `sig_len` go the same way, and their frames' bodies leak the
same (`body_ct`): `verify_ct`.
-/

@[expose] public section

namespace VG.Proof.SlhDsa.X86_64.VerifyTop

open VG VG.X86_64
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.Sha3.X86_64 (wp_movm wp_mov32i)

theorem vleak_inj : ∀ {a b : List Byte}, leakBytes a = leakBytes b → a = b
  | [], [], _ => rfl
  | x :: a, y :: b, h => by
    simp only [leakBytes, List.map_cons, List.cons.injEq] at h
    rw [BitVec.eq_of_toNat_eq h.1, vleak_inj h.2]
  | [], _ :: _, h => by simp [leakBytes] at h
  | _ :: _, [], h => by simp [leakBytes] at h

/-- `verify`'s first block: the stack's arguments loaded, and `ctx_len` compared with 256. -/
theorem top1_ok {p : Params} {st : Nat} {s : State} (h : VPre p st s) :
    WP isa (.block [.mov .r10 (.mem (Impl.SlhDsa.X86_64.Shake.stk 8)),
      .mov .r11 (.mem (Impl.SlhDsa.X86_64.Shake.stk 16)), .mov32 .rax (.imm 0), .alu .cmp .r8 (.imm 256)]) s
      fun s₄ => VMov s s₄ ∧ isa.eval .b s₄ = some (decide ((s.gpr .r8).toNat < 256)) := by
  have hin : ∀ {d : Nat}, 8 ≤ d → d + 8 ≤ 24 → InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 d) 8 :=
    fun {d} hd8 hd =>
    ⟨vArgs s, by rw [h.rd]; simp, by
      rw [show s.gpr .rsp + BitVec.ofNat 64 d = stackArgAddr s 0 + BitVec.ofNat 64 (d - 8) by
        rw [stackArgAddr_eq, BitVec.add_assoc, BitVec.ofNat_add_ofNat]; congr 2; omega]
      exact Offset.contains_base _ (by omega) (by omega)⟩
  refine wp_movm (a := s.gpr .rsp + BitVec.ofNat 64 8) (by rw [ea_stk]) (hin (by omega) (by omega)) fun s₁ u₁ => ?_
  refine wp_movm (a := s.gpr .rsp + BitVec.ofNat 64 16) (by rw [ea_stk, u₁.other _ (by decide)])
    (by rw [u₁.rd, u₁.wr]; exact hin (by omega) (by omega)) fun s₂ u₂ => ?_
  refine wp_mov32i fun s₃ u₃ => Fors.wp_cmpiC fun s₄ g₄ m₄ r₄ w₄ z₄ c₄ => WP.block_nil ?_
  have hr8 : (BitVec.signExtend 64 (256 : BitVec 32)).toNat = 256 := by decide
  rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hr8] at c₄
  refine ⟨⟨?_, ?_, ?_, fun r h1 h2 h3 => ?_, by rw [m₄, u₃.mem, u₂.mem, u₁.mem], by rw [r₄, u₃.rd, u₂.rd, u₁.rd],
    by rw [w₄, u₃.wr, u₂.wr, u₁.wr]⟩, by rw [ForsCT.eval_b', c₄]⟩
  · rw [g₄, u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]; rfl
  · rw [g₄, u₃.other _ (by decide), u₂.gpr, u₁.mem]; rfl
  · rw [g₄, u₃.gpr]; rfl
  · rw [g₄, u₃.other _ h3, u₂.other _ h2, u₁.other _ h1]

/-- The comparison of `sig_len`. -/
theorem cmpSig_ok {p : Params} (hp : VPar p) {s s₄ : State} (hm : VMov s s₄) :
    WP isa (.block [.alu .cmp .r10 (.imm (BitVec.ofNat 32 p.sigLen))]) s₄
      fun s₅ => VMov s s₅ ∧ isa.eval .e s₅ = some (decide (stackArg s 0 = BitVec.ofNat 64 p.sigLen)) := by
  have hsl31 := hp.sigLt
  obtain ⟨h10, h11, hax, hg₄, hm₄, hr₄, hw₄⟩ := hm
  refine Fors.wp_cmpiC fun s₅ g₅ m₅ r₅ w₅ z₅ _ => WP.block_nil ⟨⟨by rw [g₅, h10], by rw [g₅, h11], by rw [g₅, hax],
    fun r h1 h2 h3 => by rw [g₅, hg₄ r h1 h2 h3], by rw [m₅, hm₄], by rw [r₅, hr₄], by rw [w₅, hw₄]⟩, ?_⟩
  rw [h10, Levels.sx_ofNat hsl31] at z₅
  rw [ForsCT.eval_e', z₅]; congr 1
  by_cases e : stackArg s 0 = BitVec.ofNat 64 p.sigLen
  · simp [e]
  · have : stackArg s 0 - BitVec.ofNat 64 p.sigLen ≠ 0 := fun h0 => e (by
      have := BitVec.sub_add_cancel (stackArg s 0) (BitVec.ofNat 64 p.sigLen)
      rw [h0] at this; simpa using this.symm)
    simp [e]; exact this

theorem ct_nil {P : State → State → Prop} : RelCT isa P (.block []) fun _ _ => True :=
  Levels.taintR [] (fun _ _ _ _ h => absurd h List.not_mem_nil) (by taint_decide)

/-- After the test of `ctx_len`: two runs with the same layout and inputs. -/
theorem inner_ct {p : Params} (hS : S6 p) {f : Impl.SlhDsa.X86_64.Shake.Fns} (T : Thash4Impl p.n)
    (ht : f.t4 = T.code) (hmx : (Impl.SlhDsa.X86_64.Verify.forsPk p f).allInstrs (fun i => !loadsMxcsr i) = true)
    (hsp : NoSp (Impl.SlhDsa.X86_64.Verify.forsPk p f)) (gv : Impl.SlhDsa.X86_64.Verify.VFns) {st : Nat}
    (hst : T.stack + 16 ≤ st) (hst62 : st < 2 ^ 62) {s₁ s₂ : State} (q₁ : VPre p st s₁) (q₂ : VPre p st s₂)
    (h8₁ : (s₁.gpr .r8).toNat < 256) (eL : vlay p st s₁ = vlay p st s₂)
    (hI : Inp (vlay p st s₁) s₁.mem s₂.mem) (ea0 : stackArg s₁ 0 = stackArg s₂ 0)
    (esp : s₁.gpr .rsp = s₂.gpr .rsp) :
    RelCT isa (fun a b => VMov s₁ a ∧ VMov s₂ b)
      (.seq (.block [.alu .cmp .r10 (.imm (BitVec.ofNat 32 p.sigLen))])
        (.ite .e (.frame (.push Impl.SlhDsa.X86_64.Verify.verifyRegs) (Impl.SlhDsa.X86_64.Verify.verifyBody p f gv)
          (.pop .r11 9)) (.block []))) fun _ _ => True := by
  have hp := hS.par
  have hst16 : 16 ≤ st := by omega
  have hsl31 := hp.sigLt
  refine Levels.relSeq (ct_cmpSig hS fun _ _ _ _ h => absurd h List.not_mem_nil) (fun a ha => cmpSig_ok hp ha)
    (fun b hb => cmpSig_ok hp hb) ?_
  refine RelCT.ite (fun x y ⟨hx, hy⟩ => by rw [hx.2, hy.2, ea0]) ?_ ct_nil
  refine fun a b u₁ u₂ a' b' ⟨⟨ha, hb⟩, hc⟩ ea eb => ?_
  have hsg : ∀ {s : State}, stackArg s 0 = BitVec.ofNat 64 p.sigLen → (stackArg s 0).toNat = p.sigLen := fun e => by
    rw [e, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hsg₁ : (stackArg s₁ 0).toNat = p.sigLen := hsg (by rw [ha.2] at hc; simpa using hc)
  have hL := vlay_ok hp q₁ h8₁ hst16 hst62
  refine RelCT.frame (R := fun _ _ => True) (P := fun a b => VMov s₁ a ∧ VMov s₂ b) (fun x y ⟨hx, hy⟩ => by
      rw [hx.2.2.2.1 _ (by decide) (by decide) (by decide), hy.2.2.2.1 _ (by decide) (by decide) (by decide), esp])
    ?_ a b u₁ u₂ a' b' ⟨ha.1, hb.1⟩ ea eb
  refine fun a b u₁ u₂ a' b' ⟨x, y, ⟨hx, hy⟩, hxa, hyb⟩ ea eb => ?_
  subst hxa hyb
  exact body_ct hS T ht hmx hsp hst hL rfl hsg₁ gv hI _ _ _ _ _ _
    ⟨pushed_ok hp q₁ hst16 hx, by rw [eL]; exact pushed_ok hp q₂ hst16 hy⟩ ea eb

/-- Two runs whose public data agree have the same inputs. -/
theorem inp_of {p : Params} (hp : VPar p) {st : Nat} {s₁ s₂ : State}
    (elk : leakBytes (bytesAt s₁.mem (s₁.gpr .rdi) p.pkLen ++ bytesAt s₁.mem (s₁.gpr .rsi) (s₁.gpr .rdx).toNat ++
        bytesAt s₁.mem (s₁.gpr .rcx) (s₁.gpr .r8).toNat ++ bytesAt s₁.mem (s₁.gpr .r9) (stackArg s₁ 0).toNat) =
      leakBytes (bytesAt s₂.mem (s₂.gpr .rdi) p.pkLen ++ bytesAt s₂.mem (s₂.gpr .rsi) (s₂.gpr .rdx).toNat ++
        bytesAt s₂.mem (s₂.gpr .rcx) (s₂.gpr .r8).toNat ++ bytesAt s₂.mem (s₂.gpr .r9) (stackArg s₂ 0).toNat))
    (edi : s₁.gpr .rdi = s₂.gpr .rdi) (esi : s₁.gpr .rsi = s₂.gpr .rsi) (edx : s₁.gpr .rdx = s₂.gpr .rdx)
    (ecx : s₁.gpr .rcx = s₂.gpr .rcx) (er8 : s₁.gpr .r8 = s₂.gpr .r8) (er9 : s₁.gpr .r9 = s₂.gpr .r9)
    (ea0 : stackArg s₁ 0 = stackArg s₂ 0) : Inp (vlay p st s₁) s₁.mem s₂.mem := by
  have e := vleak_inj elk
  rw [← edi, ← esi, ← edx, ← ecx, ← er8, ← er9, ← ea0] at e
  obtain ⟨e3, eSig⟩ := List.append_inj e (by simp only [List.length_append, bytesAt_len])
  obtain ⟨e2, eCtx⟩ := List.append_inj e3 (by simp only [List.length_append, bytesAt_len])
  obtain ⟨ePk, eMsg⟩ := List.append_inj e2 (by simp only [bytesAt_len])
  have hpk := hp.pk
  refine ⟨?_, ?_, eMsg, eCtx, eSig⟩
  · show bytesAt s₁.mem (s₁.gpr .rdi) p.n = bytesAt s₂.mem (s₁.gpr .rdi) p.n
    rw [← bytesAt_take' _ _ (show p.n ≤ p.pkLen by omega), ← bytesAt_take' _ _ (show p.n ≤ p.pkLen by omega), ePk]
  · show bytesAt s₁.mem (s₁.gpr .rdi + BitVec.ofNat 64 p.n) p.n = bytesAt s₂.mem (s₁.gpr .rdi + BitVec.ofNat 64 p.n) p.n
    rw [← bytesAt_drop_take _ _ (show p.n + p.n ≤ p.pkLen by omega),
      ← bytesAt_drop_take _ _ (show p.n + p.n ≤ p.pkLen by omega), ePk]

/-- `verify` is constant time: its timing depends only on its public data. -/
theorem verify_ct {p : Params} (hS : S6 p) {f : Impl.SlhDsa.X86_64.Shake.Fns} (T : Thash4Impl p.n)
    (ht : f.t4 = T.code) (hmx : (Impl.SlhDsa.X86_64.Verify.forsPk p f).allInstrs (fun i => !loadsMxcsr i) = true)
    (hsp : NoSp (Impl.SlhDsa.X86_64.Verify.forsPk p f)) (gv : Impl.SlhDsa.X86_64.Verify.VFns) {st : Nat}
    (hst : T.stack + 16 ≤ st) (hst62 : st < 2 ^ 62) :
    ConstantTime isa (verifyContract p X86_64.abi (st + 80)).pre (verifyContract p X86_64.abi (st + 80)).pub
      (Impl.SlhDsa.X86_64.Verify.verify p f gv) := by
  have hp := hS.par
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂
  have q₁ := vPre_of h₁
  have q₂ := vPre_of h₂
  rw [show st + 80 = (st + 79) + 1 from rfl] at hpub
  sig_pub [verifyContract, verifySig, X86_64.abi, X86_64.argRegs, List.range, List.range.loop] at hpub
  obtain ⟨esp, elk, edi, esi, edx, ecx, er8, er9, ea0, ea1⟩ := hpub
  have eL : vlay p st s₁ = vlay p st s₂ := by simp only [vlay, esp, edi, esi, edx, ecx, er8, er9, ea0, ea1]
  have hI := inp_of (st := st) hp elk edi esi edx ecx er8 er9 ea0
  have hct : RelCT isa (fun a b => a = s₁ ∧ b = s₂) (Impl.SlhDsa.X86_64.Verify.verify p f gv) fun _ _ => True := by
    unfold Impl.SlhDsa.X86_64.Verify.verify
    refine Levels.relSeq (ct_top1 fun x y ⟨hx, hy⟩ r hr => by
        simp only [List.mem_singleton] at hr; subst hr hx hy; exact esp)
      (fun a ha => by subst ha; exact top1_ok q₁) (fun b hb => by subst hb; exact top1_ok q₂) ?_
    refine RelCT.ite (fun x y ⟨hx, hy⟩ => by rw [hx.2, hy.2, er8]) ?_ ct_nil
    refine fun a b u₁ u₂ a' b' ⟨⟨ha, hb⟩, hc⟩ ea eb => ?_
    have h8₁ : (s₁.gpr .r8).toNat < 256 := by rw [ha.2] at hc; simpa using hc
    exact inner_ct hS T ht hmx hsp gv hst hst62 q₁ q₂ h8₁ eL hI ea0 esp _ _ _ _ _ _ ⟨ha.1, hb.1⟩ ea eb
  exact (hct _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.SlhDsa.X86_64.VerifyTop
