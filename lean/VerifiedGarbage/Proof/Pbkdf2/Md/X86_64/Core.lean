module

public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Pbkdf2CT
public import VerifiedGarbage.Proof.Pbkdf2.Contract
public import VerifiedGarbage.Proof.Hmac.Contract
public import VerifiedGarbage.Proof.Pbkdf2.X86_64.Iterate
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Pbkdf2.Generic
import VerifiedGarbage.Proof.Hmac.Generic.Implies
import VerifiedGarbage.Proof.Pbkdf2.Memory
import VerifiedGarbage.Proof.Framework.OmegaLit
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Common
public import VerifiedGarbage.Proof.Pbkdf2.MdKeys
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hash
import VerifiedGarbage.Proof.Pbkdf2.X86_64.Copy
import VerifiedGarbage.Proof.MdStream.X86_64.Words
import VerifiedGarbage.Proof.MdStream.X86_64.PadExec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Words
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.PadW
import VerifiedGarbage.Proof.Hmac.Generic.Common
import VerifiedGarbage.Proof.Sha256.X86_64.Compress
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.X86_64.Depth

/-! ### `Pbkdf2.X86_64.IterateCT`, which only this module used -/

section

/-!
# PBKDF2-HMAC's iteration over a Merkle–Damgård hash function on x86-64: constant time

This holds for any compression function (`CalleeOk`), so it is proven once
for every implementation. The taint analysis cannot prove it without
looking into the compression function: it saves and restores our registers
in memory it also writes secrets to, so across a call the analysis forgets
that our pointers are public. So we relate two runs (`RelCT`): at every
point, correctness determines our registers from the public arguments
alone, so they agree; between the calls, the taint analysis proves each
block constant time from that (`Checks`, evaluated for each hash function,
since the code depends on its sizes); and the calls are constant time by
the compression function's own proof (`compressAt_rel`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.X86_64

open VG VG.X86_64
open VG.Impl.MdStream.X86_64 (Params restore compressAt)
open VG.Impl.Pbkdf2.X86_64 (loadKey xorW compressBlock body prologue iterate)
open VG.Proof.MdStream (Md)
open VG.Proof.MdStream.X86_64 (Shape CalleeOk compressAt_rel wp_mov)
open VG.Spec.Sha256 (bytesAt)
open VG.Spec.Hmac (StreamingHash)

/-- The registers the blocks between the calls use. -/
abbrev regsS : List Reg := [.rbx, .rbp, .r12, .r13, .r15, .rsp, .r14]

/-- The taint checks of the pieces of `iterate` between its calls, which
depend on the hash function's sizes, its length field and its digest. -/
structure Checks (P : Params) (D : Nat) : Prop where
  pro : ∃ hc, (taint.check (Taint.ofRegs [.rdi, .rsi, .rcx, .r8, .rsp]) (.block (prologue P D)) hc).isSome = true
  load : ∃ hc, (taint.check (Taint.ofRegs regsS) (.block (loadKey P 0)) hc).isSome = true
  arg : ∃ hc, (taint.check (Taint.ofRegs regsS) (.block [.mov .rsi (.reg .rbp)]) hc).isSome = true
  mid : ∃ hc, (taint.check (Taint.ofRegs regsS)
    (.block (Impl.Pbkdf2.X86_64.digest P D ++ loadKey P (P.N + P.B))) hc).isSome = true
  fin : ∃ hc, (taint.check (Taint.ofRegs regsS) (.block (Impl.Pbkdf2.X86_64.digest P D ++
    (List.range (D / 4)).flatMap xorW ++ [.alu .sub .r14 (.imm 1)])) hc).isSome = true
  epi : ∃ hc, (taint.check (Taint.ofRegs [.r15]) (.block (restore P)) hc).isSome = true
  ite : ∃ hc, (taint.check (Taint.ofRegs []) (.block []) hc).isSome = true

/-- The public arguments are the same. -/
structure PubEq (s₀ s₀' : State) : Prop where
  rdi : s₀.gpr .rdi = s₀'.gpr .rdi
  rsi : s₀.gpr .rsi = s₀'.gpr .rsi
  rdx : (s₀.gpr .rdx).setWidth 32 = (s₀'.gpr .rdx).setWidth 32
  rcx : s₀.gpr .rcx = s₀'.gpr .rcx
  r8 : s₀.gpr .r8 = s₀'.gpr .r8
  rsp : s₀.gpr .rsp = s₀'.gpr .rsp

theorem PubEq.nn {s₀ s₀' : State} (hq : PubEq s₀ s₀') : nn s₀ = nn s₀' :=
  congrArg BitVec.toNat hq.rdx

/-- The state during a step, with `v` in `r14`. -/
structure St (P : Params) (D W : Nat) (H : Md P.B P.N P.L) (s₀ : State) (v : Addr) (s : State) : Prop
    extends Regs P D W s₀ s where
  r14 : s.gpr .r14 = v
  pad : bytesAt s.mem (blk P s₀ + BitVec.ofNat 64 D) (P.B - D) = H.tailPad D

section
variable {P : Params} {D W : Nat} {H : Md P.B P.N P.L}

/-- The registers the blocks use agree in two runs. -/
theorem St.agree {s₀ s₀' : State} (hq : PubEq s₀ s₀') {v : Addr} {s s' : State} (h : St P D W H s₀ v s)
    (h' : St P D W H s₀' v s') : ∀ r ∈ regsS, s.gpr r = s'.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h.rbx, h'.rbx, hv, hv, scr, scr, hq.r8]
  · rw [h.rbp, h'.rbp, blk, blk, scr, scr, hq.r8]
  · rw [h.r12, h'.r12, key, key, hq.rdi]
  · rw [h.r13, h'.r13, tp, tp, hq.rcx]
  · rw [h.r15, h'.r15, scr, scr, hq.r8]
  · rw [h.rsp, h'.rsp, hq.rsp]
  · rw [h.r14, h'.r14]

theorem St.of_inv {s₀ : State} {r : Nat} {s : State} (h : Inv P D W H s₀ (r + 1) s) :
    St P D W H s₀ (BitVec.ofNat 64 (r + 1)) s :=
  ⟨h.toRegs, h.r14, h.pad⟩

variable (hz : Sizes P D W) {s₀ : State} (hp : Pre P D W s₀) {v : Addr}
include hz hp

/-! ## What each piece of a step does, in one run -/

theorem load_st (hR : H.Reloc) {o : Nat} (ho : o + P.N ≤ 2 * (P.N + P.B)) {s : State} (h : St P D W H s₀ v s) :
    WP isa (.block (loadKey P o)) s (St P D W H s₀ v) := by
  have := so_le hz; have := N_le hz; have := B_le hz; have := hz.fits; have := hz.DN; have := hz.pad
  have := hz.NL
  rw [← List.append_nil (loadKey P o)]
  exact load_ok hz hp hR h.toRegs ho fun s' g rd wr f _ => WP.block_nil
    ⟨h.toRegs.write (fun r hr _ _ _ _ _ => g r hr) rd wr (frame_scr (a := P.so + 48) (by omega_arith) f),
      (g _ (by decide)).trans h.r14,
      (Memory.frame_bytesAt f (fun r hr => blk_disj hz hp (by omega_arith) r (by simp at hr; simp [hr])) (by omega_arith)).trans
        h.pad⟩

theorem cmp_st {name : String} {code : Prog isa} (hf : CalleeOk H code) {s : State} (h : St P D W H s₀ v s) :
    WP isa (compressBlock name code) s (St P D W H s₀ v) := by
  have := so_le hz; have := N_le hz; have := B_le hz; have := hz.fits; have := hz.DN; have := hz.pad
  have := hz.NL
  exact cmp_ok hz hp hf h.toRegs fun s' h' r14 f _ =>
    ⟨h', r14.trans h.r14, (Memory.frame_bytesAt f (blk_disj hz hp (by omega_arith)) (by omega_arith)).trans h.pad⟩

theorem mid_st (hs : Shape H) (hR : H.Reloc) {s : State} (h : St P D W H s₀ v s) :
    WP isa (.block (Impl.Pbkdf2.X86_64.digest P D ++ loadKey P (P.N + P.B))) s (St P D W H s₀ v) := by
  have := so_le hz; have := N_le hz; have := B_le hz; have := hz.fits; have := hz.NL
  refine digest_ok hz hp hs h.toRegs h.pad fun s' g rd wr f _ p => ?_
  exact load_st hz hp hR (by omega_arith)
    ⟨h.toRegs.write (fun r hr _ _ _ _ _ => g r hr) rd wr (frame_scr (a := P.so + 48 + P.N) (by omega_arith) f),
      (g _ (by decide)).trans h.r14, p⟩

/-! ## Two runs -/

variable {s₀' : State} (hp' : Pre P D W s₀') (hq : PubEq s₀ s₀')
include hp' hq

theorem cmp_rel {name : String} {code : Prog isa} (hf : CalleeOk H code) (hc : Checks P D) :
    RelCT isa (fun s s' => St P D W H s₀ v s ∧ St P D W H s₀' v s') (compressBlock name code) fun s s' =>
      St P D W H s₀ v s ∧ St P D W H s₀' v s' := by
  obtain ⟨_, ha⟩ := hc.arg
  obtain su : RelCT isa (fun s s' => St P D W H s₀ v s ∧ St P D W H s₀' v s') (.block [.mov .rsi (.reg .rbp)])
      fun s s' => (St P D W H s₀ v s ∧ s.gpr .rsi = blk P s₀) ∧ (St P D W H s₀' v s' ∧ s'.gpr .rsi = blk P s₀') :=
    ((RelCT.taint (A := taint) (Taint.ofRegs regsS) (fun _ _ h => Taint.agree_ofRegs (St.agree hq h.1 h.2)) ha).wp
      fun _ _ h => ⟨wp_mov fun s₁ u₁ _ _ => WP.block_nil ⟨⟨h.1.toRegs.write
          (fun r _ _ _ hr _ _ => u₁.other r hr) u₁.rd u₁.wr (by rw [u₁.mem]; exact Frame.refl _ _),
          (u₁.other _ (by decide)).trans h.1.r14, by rw [u₁.mem]; exact h.1.pad⟩, by rw [u₁.gpr, h.1.rbp]⟩,
        wp_mov fun s₁ u₁ _ _ => WP.block_nil ⟨⟨h.2.toRegs.write
          (fun r _ _ _ hr _ _ => u₁.other r hr) u₁.rd u₁.wr (by rw [u₁.mem]; exact Frame.refl _ _),
          (u₁.other _ (by decide)).trans h.2.r14, by rw [u₁.mem]; exact h.2.pad⟩, by rw [u₁.gpr, h.2.rbp]⟩⟩).mono
      (fun _ _ h => h) fun _ _ h => h.2
  obtain call := compressAt_rel H hf (name := name)
    (P' := fun s s' => (St P D W H s₀ v s ∧ s.gpr .rsi = blk P s₀) ∧ (St P D W H s₀' v s' ∧ s'.gpr .rsi = blk P s₀'))
    fun s s' ⟨⟨h, hsi⟩, ⟨h', hsi'⟩⟩ => by
      obtain ag := St.agree hq h h'
      exact ⟨⟨_, _, _, callOk_of hz hp h.toRegs hsi⟩, ⟨_, _, _, callOk_of hz hp' h'.toRegs hsi'⟩,
        ag _ (by simp), ag _ (by simp), by rw [hsi, hsi', blk, blk, scr, scr, hq.r8], ag _ (by simp)⟩
  exact ((su.seq call).wp fun _ _ h => ⟨cmp_st hz hp hf h.1, cmp_st hz hp' hf h.2⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2

theorem body_rel (hs : Shape H) (hR : H.Reloc) {name : String} {code : Prog isa} (hf : CalleeOk H code)
    (hc : Checks P D) {r : Nat} :
    RelCT isa (fun s s' => Inv P D W H s₀ (r + 1) s ∧ Inv P D W H s₀' (r + 1) s') (body P D name code)
      fun s s' => (eval .ne s = some (r != 0) ∧ Inv P D W H s₀ r s) ∧
        (eval .ne s' = some (r != 0) ∧ Inv P D W H s₀' r s') := by
  have := so_le hz; have := N_le hz; have := B_le hz
  obtain ⟨_, hl⟩ := hc.load
  obtain ⟨_, hm⟩ := hc.mid
  obtain ⟨_, hfi⟩ := hc.fin
  obtain l0 : RelCT isa (fun s s' => Inv P D W H s₀ (r + 1) s ∧ Inv P D W H s₀' (r + 1) s') (.block (loadKey P 0))
      fun s s' => St P D W H s₀ (BitVec.ofNat 64 (r + 1)) s ∧ St P D W H s₀' (BitVec.ofNat 64 (r + 1)) s' :=
    ((RelCT.taint (A := taint) (Taint.ofRegs regsS) (fun _ _ h =>
      Taint.agree_ofRegs (St.agree hq (St.of_inv h.1) (St.of_inv h.2))) hl).wp
      fun _ _ h => ⟨load_st hz hp hR (by omega_arith) (St.of_inv h.1), load_st hz hp' hR (by omega_arith) (St.of_inv h.2)⟩).mono
      (fun _ _ h => h) fun _ _ h => h.2
  obtain dl : RelCT isa (fun s s' => St P D W H s₀ (BitVec.ofNat 64 (r + 1)) s ∧
        St P D W H s₀' (BitVec.ofNat 64 (r + 1)) s')
      (.block (Impl.Pbkdf2.X86_64.digest P D ++ loadKey P (P.N + P.B)))
      fun s s' => St P D W H s₀ (BitVec.ofNat 64 (r + 1)) s ∧ St P D W H s₀' (BitVec.ofNat 64 (r + 1)) s' :=
    ((RelCT.taint (A := taint) (Taint.ofRegs regsS) (fun _ _ h => Taint.agree_ofRegs (St.agree hq h.1 h.2))
      hm).wp fun _ _ h => ⟨mid_st hz hp hs hR h.1, mid_st hz hp' hs hR h.2⟩).mono
      (fun _ _ h => h) fun _ _ h => h.2
  obtain fin : RelCT isa (fun s s' => St P D W H s₀ (BitVec.ofNat 64 (r + 1)) s ∧
        St P D W H s₀' (BitVec.ofNat 64 (r + 1)) s')
      (.block (Impl.Pbkdf2.X86_64.digest P D ++ (List.range (D / 4)).flatMap xorW ++ [.alu .sub .r14 (.imm 1)]))
      fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs regsS) (fun _ _ h => Taint.agree_ofRegs (St.agree hq h.1 h.2)) hfi
  obtain c := cmp_rel hz hp hp' hq (v := BitVec.ofNat 64 (r + 1)) hf hc (name := name)
  exact ((l0.seq (c.seq (dl.seq (c.seq fin)))).wp fun _ _ h =>
    ⟨body_ok hz hp hs hR hf h.1, body_ok hz hp' hs hR hf h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2

theorem loop_rel (hs : Shape H) (hR : H.Reloc) {name : String} {code : Prog isa} (hf : CalleeOk H code)
    (hc : Checks P D) {n : Nat} :
    RelCT isa (fun s s' => Inv P D W H s₀ (n + 1) s ∧ Inv P D W H s₀' (n + 1) s') (.loop (body P D name code) .ne)
      fun _ _ => True :=
  RelCT.loop (M := isa) (body := body P D name code) (c := .ne) (Q := fun _ _ => True)
    (fun m s s' => Inv P D W H s₀ (m + 1) s ∧ Inv P D W H s₀' (m + 1) s') (fun m => by
      intro s s' t t' u u' h e e'
      obtain ⟨ht, ⟨z, i⟩, ⟨z', i'⟩⟩ := body_rel hz hp hp' hq hs hR hf hc _ _ _ _ _ _ h e e'
      refine ⟨ht, z.trans z'.symm, fun _ => trivial, fun hc' => ?_⟩
      obtain hc'' : some (m != 0) = some true := z.symm.trans hc'
      cases m with
      | zero => cases hc''
      | succ m => exact ⟨m, by omega_arith, i, i'⟩) n

theorem iterate_rel {S : StreamingHash} {iv : H.HV} (ho : HashOk P D W S H iv) {name : String}
    {code : Prog isa} (hf : CalleeOk H code) (hc : Checks P D) :
    RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') (iterate P D name code) fun _ _ => True := by
  obtain ⟨_, hpr⟩ := hc.pro
  obtain ⟨_, hep⟩ := hc.epi
  obtain ⟨_, hit⟩ := hc.ite
  obtain pro : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') (.block (prologue P D)) fun s s' =>
      (Inv P D W H s₀ (nn s₀) s ∧ s.zf = some (decide (nn s₀ = 0))) ∧
      (Inv P D W H s₀' (nn s₀') s' ∧ s'.zf = some (decide (nn s₀' = 0))) :=
    ((RelCT.taint (A := taint) (Taint.ofRegs [.rdi, .rsi, .rcx, .r8, .rsp])
      (P := fun s s' => s = s₀ ∧ s' = s₀') (fun _ _ ⟨e, e'⟩ => Taint.agree_ofRegs fun r hr => by
        rw [e, e']
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · exact hq.rdi
        · exact hq.rsi
        · exact hq.rcx
        · exact hq.r8
        · exact hq.rsp) hpr).wp
      fun _ _ ⟨e, e'⟩ => by
        rw [e, e']; exact ⟨prologue_ok hz hp ho.shape ho.lenOk, prologue_ok hz hp' ho.shape ho.lenOk⟩).mono
      (fun _ _ h => h) fun _ _ h => h.2
  obtain br : RelCT isa (fun s s' =>
        (Inv P D W H s₀ (nn s₀) s ∧ s.zf = some (decide (nn s₀ = 0))) ∧
        (Inv P D W H s₀' (nn s₀') s' ∧ s'.zf = some (decide (nn s₀' = 0))))
      (.ite .e (.block []) (.loop (body P D name code) .ne))
      fun s s' => Inv P D W H s₀ 0 s ∧ Inv P D W H s₀' 0 s' := by
    refine (RelCT.ite (fun s s' h => ?_) (RelCT.taint (A := taint) (Taint.ofRegs [])
      (fun _ _ _ => Taint.agree_ofRegs (by simp)) hit) ?_).wp
      (fun _ _ h => ⟨loop_ok hz hp ho.shape ho.reloc hf h.1.1 h.1.2,
        loop_ok hz hp' ho.shape ho.reloc hf h.2.1 h.2.2⟩) |>.mono (fun _ _ h => h) fun _ _ h => h.2
    · show s.zf = s'.zf
      rw [h.1.2, h.2.2, hq.nn]
    · intro s s' t t' u u' ⟨⟨⟨i, z⟩, ⟨i', _⟩⟩, hc'⟩ e e'
      obtain hc'' : some (decide (nn s₀ = 0)) = some false := z.symm.trans hc'
      obtain hne : nn s₀ ≠ 0 := fun h0 => by rw [h0] at hc''; cases hc''
      obtain ⟨m, hm⟩ : ∃ m, nn s₀ = m + 1 := ⟨_, (Nat.succ_pred_eq_of_ne_zero hne).symm⟩
      rw [hm] at i
      rw [← hq.nn, hm] at i'
      exact loop_rel hz hp hp' hq ho.shape ho.reloc hf hc _ _ _ _ _ _ ⟨i, i'⟩ e e'
  obtain epi : RelCT isa (fun s s' => Inv P D W H s₀ 0 s ∧ Inv P D W H s₀' 0 s') (.block (restore P))
      fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs [.r15]) (fun _ _ h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [h.1.r15, h.2.r15, scr, scr, hq.r8]) hep
  exact pro.seq (br.seq epi)

end

/-! ## Verified -/

theorem pubEq_of {S : StreamingHash} {W : Nat} {s₁ s₂ : State} (h : (iterK S W).pub s₁ s₂) : PubEq s₁ s₂ :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

/-- `iterate` is verified against `iterK`, for any hash function the proof
supports (`HashOk`), whose pieces of code the taint analysis accepts
(`Checks`), and any compression function (`CalleeOk`), if it never loads
MXCSR. -/
theorem verified {P : Params} {D W : Nat} {S : StreamingHash} {H : Md P.B P.N P.L} {iv : H.HV}
    (ho : HashOk P D W S H iv) (hc : Checks P D) {name : String} {code : Prog isa} (hf : CalleeOk H code)
    (hm : (iterate P D name code).allInstrs (fun i => !loadsMxcsr i) = true)
    (hsat : ∃ s, (iterK S W).pre s) :
    Verified X86_64.target (iterate P D name code) (iterK S W) := by
  refine ⟨iterate_ok ho hf hm, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, hsat⟩
  exact (iterate_rel ho.sizes (pre_of ho.link.hS ho.link.hD h₁) (pre_of ho.link.hS ho.link.hD h₂)
    (pubEq_of hpub) ho hf hc _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-- `iterK` implies the shared contract, for any hash function and scratch
space, given that the shared contract is satisfiable. -/
theorem iterImp (S : StreamingHash) (W : Nat) (h : ∃ s, (Proof.Pbkdf2.iterateContract S W X86_64.abi 8).pre s) :
    (iterK S W).Implies (Proof.Pbkdf2.iterateContract S W X86_64.abi 8) := by
  generic_implies [
    Proof.Pbkdf2.iterateContract, Proof.Pbkdf2.iterateSig, iterK, X86_64.abi, X86_64.argRegs] using h

/-- A state satisfying `iterate`'s precondition, with states of `S` bytes, a
digest of `D` bytes and `8 W` bytes of scratch space. -/
def iterSat (S D W : Nat) : State where
  gpr r := match r with
    | .rdi => 0x10000 | .rsi => 0x20000 | .rcx => 0x30000 | .r8 => 0x40000
    | .rsp => 0x90000
    | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x10000, 2 * S⟩, ⟨0x20000, D⟩]
  wr := [⟨0x30000, D⟩, ⟨0x40000, 8 * W⟩]

end VG.Proof.Pbkdf2.X86_64

end

end

/-! ### `Pbkdf2.Md.X86_64.HmacInit`, which only this module used -/

section

/-!
# HMAC over any Merkle–Damgård hash function on x86-64: `init`

HMAC's `init` (`Impl/Pbkdf2/Md/X86_64.lean`) saves our caller's registers
(`pro_ok`), sets each state's hash value with the streaming `init`
(`callInit_ok`), writes `K₀ ⊕ ipad` into the inner state's buffer and
`K₀ ⊕ opad` into the outer one's (`keys_ok`: `ipad` sixteen bytes at a
time, `fill_ok`; the key XORed in, its whole 16-byte words, `key16_ok`, then
its other bytes, `key_ok`; then the outer buffer from the inner one sixteen
bytes at a time, `opad_ok`), compresses each buffer into its state's hash value, and loads our
caller's registers back. The compressions are `Hash.compBoth`, of which
`init` needs `BothOk`: the compression function on each buffer in turn
(`BothOk.twice`, from `cmp_ok`), or one call of a function that compresses
both at once (`BothOk.pair`, from `MdStream.X86_64.PairOk`), whichever the
hash function's code has (`HashOK.both`, `bothOk`). A state whose initial hash value has
absorbed the block in its buffer represents that block
(`Md.repr_block`). Constant time: the taint analysis checks the pieces
between the calls (`Checks`); the calls are constant time by the callees'
own proofs.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Md.X86_64.HmacInit

open VG.X86_64 VG.Proof.MdStream
open VG.Proof.MdStream.X86_64 (add_ofNat sx_ofNat zx_ofNat wp_mov wp_mov32i wp_addi wp_andi
  wp_store8 wp_movzx8 wp_cmp Upd CallOk compressAt_ok compressAt_rel ea_at ofInt_natCast
  ofNat_succ ofNat_pred ofNat_beq_zero sub_beq and_mask vbytes vbytes_length vbytes_getElem wp_movqx wp_xbin
  wp_movImm64' wp_movdquStoreX wp_shrX wp_testX WP.cons)
open VG.Impl.MdStream.X86_64 (compressAt at_)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash byteAt pairArgs)
open VG.Proof.Pbkdf2.X86_64 (ea_off)
open VG.Proof.Pbkdf2.Md.X86_64.Calls (initG rel_taint rel_wp init_call init_rel SavedRegs saveR save_ok
  restore_ok count_loop ea_byteAt sx_one wp_xor32i xor_byte PubEq args repr_keep)
open VG.Proof.Hmac.Generic.Common (K0 K0_length covers_one InRegions.right' bytes_keep)
open VG.Proof.Hmac.Common (bytesAt_length bytesAt_getD' bytesAt_writeBytes_sep bytesAt_add extractLsb'_read)
open VG.Proof.Hmac.Generic.Common (bytesAt_writeBytes_self')
open VG.Proof.Pbkdf2.MdKeys (ipadBlk ipadBlk_length ipadBlk_zero ipadBlk_succ ipadBlk_eq writeBytes_set
  xorOpad_ipad)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil writeBytes_frame)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (xorPad ipad opad blockKey)

/-! ## The precondition -/

section
variable (H : Hash) (s₀ : State)

abbrev inn : Addr := s₀.gpr .rdi
abbrev out : Addr := s₀.gpr .rsi
abbrev kp : Addr := s₀.gpr .rdx
abbrev kl : Nat := (s₀.gpr .rcx).toNat
abbrev scr : Addr := s₀.gpr .r8
abbrev inR : Region := ⟨inn s₀, H.S⟩
abbrev outR : Region := ⟨out s₀, H.S⟩
abbrev keyR : Region := ⟨kp s₀, kl s₀⟩
abbrev retR : Region := ⟨s₀.gpr .rsp, 8⟩
abbrev stkR : Region := below (s₀.gpr .rsp) 16
/-- The compression function's working space. -/
abbrev calR : Region := ⟨scr s₀, H.P.so⟩
/-- Where our caller's registers are saved. -/
abbrev svR : Region := saveR H.stream (scr s₀)
/-- The buffer of the state at `p`. -/
abbrev bufOf (p : Addr) : Addr := p + BitVec.ofNat 64 H.P.N
/-- The key, padded to a block. -/
abbrev k0 : List Byte := K0 s₀.mem (kp s₀) (kl s₀) H.P.B

end

abbrev scR (sc : Nat) (s₀ : State) : Region := ⟨scr s₀, 8 * sc⟩

/-- The precondition, with the sizes of `H`. -/
structure Pre (H : Hash) (sc : Nat) (s₀ : State) : Prop where
  kl_le : kl s₀ ≤ H.P.B
  rd : s₀.rd = [keyR s₀]
  wr : s₀.wr = [inR H s₀, outR H s₀, scR sc s₀]
  i_o : (inR H s₀).Disjoint (outR H s₀)
  i_s : (inR H s₀).Disjoint (scR sc s₀)
  o_s : (outR H s₀).Disjoint (scR sc s₀)
  k_i : (keyR s₀).Disjoint (inR H s₀)
  k_o : (keyR s₀).Disjoint (outR H s₀)
  k_s : (keyR s₀).Disjoint (scR sc s₀)
  ret_i : (retR s₀).Disjoint (inR H s₀)
  ret_o : (retR s₀).Disjoint (outR H s₀)
  ret_s : (retR s₀).Disjoint (scR sc s₀)
  stk_i : (stkR s₀).Disjoint (inR H s₀)
  stk_o : (stkR s₀).Disjoint (outR H s₀)
  stk_k : (stkR s₀).Disjoint (keyR s₀)
  stk_s : (stkR s₀).Disjoint (scR sc s₀)
  nw : (scr s₀).toNat + 8 * sc ≤ 2 ^ 64
  fits : H.stream.buf ≤ 8 * sc

variable {H : Hash} (hH : HashOK H)

theorem pre_of {sc : Nat} {s₀ : State} (h : (initG hH.SH sc).pre s₀) (hfit : H.stream.buf ≤ 8 * sc) :
    Pre H sc s₀ := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := h
  have hS := hH.hS
  have hB := hH.hB
  simp only [hS, hB] at *
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, hfit⟩

section
variable {sc : Nat} {s₀ : State} (hp : Pre H sc s₀)
include hH hp

/-- The sizes the proof needs. -/
theorem sizes : H.P.N % 4 = 0 ∧ H.P.B % 4 = 0 ∧ H.P.N ≤ 64 ∧ 0 < H.P.B ∧ H.P.B ≤ 128 ∧
    H.P.so + 48 = 8 * H.stream.W ∧ H.stream.buf = 8 * H.stream.W + 48 ∧ H.stream.W ≤ 256 ∧
    8 * H.stream.W + 48 ≤ 8 * sc ∧ 8 * sc ≤ 2 ^ 64 := by
  have := hH.hN4; have := hH.N_le; have := hH.B_le; have := hH.B_pos; have := hH.hso; have := hp.nw
  have := hp.fits
  have hb : H.stream.buf = 8 * H.stream.W + 48 := rfl
  have hw : H.stream.W = (H.P.so + 48) / 8 := rfl
  have : H.P.B % 4 = 0 := by rcases hH.dims.B with h | h <;> omega_using [h]
  omega_arith

/-! ## The parts of the regions -/

theorem save_sub : Region.Sub (svR H s₀) (scR sc s₀) := by
  obtain ⟨-, -, -, -, -, -, -, -, h, -⟩ := sizes hH hp
  exact Offset.sub_base _ h

theorem cal_sub : Region.Sub (calR H s₀) (scR sc s₀) := by
  obtain ⟨-, -, -, -, -, h, -, -, h', -⟩ := sizes hH hp
  exact Region.sub_prefix (by omega_using [h, h'])

theorem cal_save : (calR H s₀).Disjoint (svR H s₀) := by
  obtain ⟨-, -, -, -, -, h, -, -, h', h''⟩ := sizes hH hp
  have := hp.nw
  exact Offset.base_disjoint _ (by omega_using [h]) (by omega_using [h', this])

omit hH hp in
theorem stk_ret : (stkR s₀).Disjoint (retR s₀) :=
  Offset.below_disjoint _ (m := 16) (by omega_using [])

/-- What a state's region is: writable, and apart from the others. -/
structure StOk (p : Addr) : Prop where
  mem : ⟨p, H.S⟩ ∈ s₀.wr
  sc : Region.Disjoint ⟨p, H.S⟩ (scR sc s₀)
  stk : (stkR s₀).Disjoint ⟨p, H.S⟩
  ret : (retR s₀).Disjoint ⟨p, H.S⟩
  key : (keyR s₀).Disjoint ⟨p, H.S⟩

omit hH in
theorem stOk_in : StOk (H := H) (sc := sc) (s₀ := s₀) (inn s₀) :=
  ⟨by rw [hp.wr]; simp, hp.i_s, hp.stk_i, hp.ret_i, hp.k_i⟩

omit hH in
theorem stOk_out : StOk (H := H) (sc := sc) (s₀ := s₀) (out s₀) :=
  ⟨by rw [hp.wr]; simp, hp.o_s, hp.stk_o, hp.ret_o, hp.k_o⟩

/-- A region the code may write while our caller's registers, the return
address and the key stay put. -/
structure Away (r : Region) : Prop where
  sv : (svR H s₀).Disjoint r
  ret : (retR s₀).Disjoint r
  key : (keyR s₀).Disjoint r

theorem away_st {p : Addr} (hs : StOk (H := H) (sc := sc) (s₀ := s₀) p) {r : Region}
    (h : Region.Sub r ⟨p, H.S⟩) : Away (H := H) (s₀ := s₀) r :=
  ⟨(hs.sc.symm.sub_left (save_sub hH hp)).sub_right h, hs.ret.sub_right h, hs.key.sub_right h⟩

theorem away_cal : Away (H := H) (s₀ := s₀) (calR H s₀) :=
  ⟨(cal_save hH hp).symm, hp.ret_s.sub_right (cal_sub hH hp), hp.k_s.sub_right (cal_sub hH hp)⟩

theorem away_stk {r : Region} (h : Region.Sub r (stkR s₀)) : Away (H := H) (s₀ := s₀) r :=
  ⟨(hp.stk_s.symm.sub_left (save_sub hH hp)).sub_right h, stk_ret.symm.sub_right h, hp.stk_k.symm.sub_right h⟩

end

/-! ## What holds from the prologue on -/

/-- The registers and memory kept from the prologue on, with `rbx = b` (the
state being compressed). -/
structure KR (H : Hash) (s₀ : State) (b : Addr) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rbx : s.gpr .rbx = b
  rbp : s.gpr .rbp = kp s₀
  r12 : s.gpr .r12 = out s₀
  r13 : s.gpr .r13 = s₀.gpr .rcx
  r15 : s.gpr .r15 = scr s₀
  saved : SavedRegs H.stream (scr s₀) s₀ s.mem
  ret : s.mem.readW (s₀.gpr .rsp) 64 = s₀.mem.readW (s₀.gpr .rsp) 64
  key : ∀ i < kl s₀, s.mem (kp s₀ + BitVec.ofNat 64 i) = s₀.mem (kp s₀ + BitVec.ofNat 64 i)

/-- The registers `KR` fixes. -/
abbrev kregs : List Reg := [.rbx, .rbp, .r12, .r13, .r15, .rsp]

theorem KR.keep {s₀ s s' : State} {b : Addr} (h : KR H s₀ b s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r ∈ kregs, s'.gpr r = s.gpr r) {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (ha : ∀ r ∈ rs, Away (H := H) (s₀ := s₀) r) : KR H s₀ b s' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, (hg _ (by simp)).trans h.rsp, (hg _ (by simp)).trans h.rbx,
    (hg _ (by simp)).trans h.rbp, (hg _ (by simp)).trans h.r12, (hg _ (by simp)).trans h.r13,
    (hg _ (by simp)).trans h.r15, h.saved.frame H.stream hf fun r hr => (ha r hr).sv,
    (hf.readW (r := retR s₀) (Region.contains_self _ _) (fun r hr => (ha r hr).ret) (by decide)).trans h.ret,
    fun i hi => (hf.bytes (R := keyR s₀) (fun r hr => (ha r hr).key) (Nat.le_of_lt (s₀.gpr .rcx).isLt)
      hi).trans (h.key i hi)⟩

theorem KR.regs {s₀ s s' : State} {b : Addr} (h : KR H s₀ b s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r ∈ kregs, s'.gpr r = s.gpr r) (hm : s'.mem = s.mem) : KR H s₀ b s' :=
  h.keep (rs := []) hrd hwr hg (by rw [hm]; exact Frame.refl _ _) (by simp)

/-! ## The prologue -/

section
variable {sc : Nat} {s₀ : State} (hp : Pre H sc s₀)
include hH hp

theorem pro_ok : WP isa (.block H.initPrologue) s₀ (KR H s₀ (inn s₀)) := by
  obtain ⟨-, -, -, -, -, -, -, hW, hL, -⟩ := sizes hH hp
  unfold Hash.initPrologue
  refine save_ok H.stream (scr := scr s₀) rfl hW (by rw [hp.wr]; simp) hL fun s₁ g₁ rd₁ wr₁ f₁ sv₁ => ?_
  refine wp_mov fun s₂ u₂ _ _ => wp_mov fun s₃ u₃ _ _ => wp_mov fun s₄ u₄ _ _ => wp_mov fun s₅ u₅ _ _ =>
    wp_mov fun s₆ u₆ _ _ => WP.block_nil ?_
  obtain hm : s₆.mem = s₁.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem]
  obtain g : ∀ r, r ∉ [Reg.rbx, .r12, .r15, .rbp, .r13] → s₆.gpr r = s₀.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₆.other r hr.2.2.2.2, u₅.other r hr.2.2.2.1, u₄.other r hr.2.2.1, u₃.other r hr.2.1, u₂.other r hr.1, g₁]
  obtain hs : ∀ r ∈ [svR H s₀], (retR s₀).Disjoint r ∧ (keyR s₀).Disjoint r := by
    simp only [List.mem_singleton]; rintro r rfl
    exact ⟨hp.ret_s.sub_right (save_sub hH hp), hp.k_s.sub_right (save_sub hH hp)⟩
  exact ⟨by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁], by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁],
    g _ (by decide),
    by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.gpr, g₁],
    by rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), g₁],
    by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
      u₂.other _ (by decide), g₁],
    by rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), g₁],
    by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), g₁],
    hm ▸ sv₁,
    by rw [hm]; exact f₁.readW (r := retR s₀) (Region.contains_self _ _) (fun r hr => (hs r hr).1) (by decide),
    fun i hi => by
      rw [hm]; exact f₁.bytes (R := keyR s₀) (fun r hr => (hs r hr).2) (Nat.le_of_lt (s₀.gpr .rcx).isLt) hi⟩

end

/-! ## The calls of the streaming `init` -/

section
variable {sc : Nat} {s₀ : State} (hp : Pre H sc s₀)
include hH hp

/-- A call of the streaming `init` on the state at `p`, from the register `st`. -/
theorem callInit_ok {b : Addr} {s : State} (hk : KR H s₀ b s) {st : Reg} {p : Addr} (hs : s.gpr st = p)
    (hst : StOk (H := H) (sc := sc) (s₀ := s₀) p) {Q : State → Prop}
    (hQ : ∀ s', KR H s₀ b s' → Frame [⟨p, H.S⟩, stkR s₀] s.mem s'.mem → hH.SH.Repr s'.mem p [] → Q s') :
    WP isa (H.stream.callInit st) s Q := by
  refine WP.seq (wp_mov fun s₁ u₁ _ _ => WP.block_nil ?_)
  obtain k₁ : KR H s₀ b s₁ := hk.regs u₁.rd u₁.wr (fun r hr => u₁.other r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) u₁.mem
  refine init_call hH.stream (st := p) (by rw [u₁.gpr, hs]) (by rw [k₁.wr]; exact covers_one hst.mem)
    (by rw [k₁.rsp]; exact hst.stk) fun s' ha hr => ?_
  have f := ha.frame
  rw [k₁.rsp, u₁.mem] at f
  refine hQ s' (k₁.keep ha.rd ha.wr (fun r hr => ha.cs r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [calleeSaved])) (u₁.mem ▸ f) ?_) f hr
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact away_st hH hp hst (fun _ h => h)
  · exact away_stk hH hp (fun _ h => h)

end

/-! ## The padded keys -/

/-- The 128 bits whose low and high halves are both `c` (`Hash.padConst`). -/
def rep16 (c : BitVec 64) : BitVec 128 :=
  XBinOp.eval .punpcklqdq ((0 : BitVec 64) ++ c) ((0 : BitVec 64) ++ c)

theorem vbytes_ipad : vbytes (rep16 0x3636363636363636) = List.replicate 16 ipad := by decide

theorem vbytes_x6a : vbytes (rep16 0x6a6a6a6a6a6a6a6a) = List.replicate 16 (0x6a : Byte) := by decide

/-- A 16-byte store writes the register's bytes. -/
theorem store16 (m : Mem) (a : Addr) (v : BitVec 128) : m.writeW a v = writeBytes m a (vbytes v) :=
  Pbkdf2.Memory.writeW_bytes m a v _ (by simp only [Nat.reduceDiv, Nat.reduceMul, BitVec.setWidth_eq]; rfl)

/-- The bytes of 16 bytes XORed with one byte repeated. -/
theorem vbytes_xor (x c : BitVec 128) (b : Byte) (h : vbytes c = List.replicate 16 b) :
    vbytes (x ^^^ c) = (vbytes x).map (· ^^^ b) := by
  apply List.ext_getElem (by simp only [vbytes_length, List.length_map])
  intro i h₁ h₂
  obtain hi : i < 16 := by rwa [vbytes_length] at h₁
  obtain hc : byte c i = b := by
    rw [← vbytes_getElem c (i := i) (by rwa [vbytes_length])]
    simp only [h, List.getElem_replicate]
  rw [List.getElem_map, vbytes_getElem, vbytes_getElem, ← hc]
  exact BitVec.extractLsb'_xor

/-- The bytes of 16 bytes loaded from memory. -/
theorem vbytes_readW (m : Mem) (a : Addr) : vbytes (m.readW a 128) = bytesAt m a 16 := by
  simp only [vbytes, bytesAt]
  refine List.map_congr_left fun j hj => ?_
  obtain hj := List.mem_range.mp hj
  simp only [byte, Mem.readW, BitVec.setWidth_eq]
  exact extractLsb'_read _ _ hj

/-- Bytes written inside bytes written before: those, in place. -/
theorem writeBytes_over (m : Mem) (q : Addr) (xs ys zs : List Byte) {j : Nat}
    (hx : xs.length < 2 ^ 63) (hy : j + ys.length ≤ xs.length) (hz : zs.length = xs.length)
    (h : ∀ i < xs.length, zs.getD i 0 = if j ≤ i ∧ i < j + ys.length then ys.getD (i - j) 0 else xs.getD i 0) :
    writeBytes (writeBytes m q xs) (q + BitVec.ofNat 64 j) ys = writeBytes m q zs := by
  funext a
  obtain hd := (a - q).isLt
  simp only [writeBytes, Offset.sub_add_eq, Offset.toNat_sub_ofNat, hz]
  generalize (a - q).toNat = d at hd ⊢
  rw [Nat.mod_eq_of_lt (a := j) (by omega_using [hx, hy])]
  by_cases hdj : j ≤ d
  · rw [show 2 ^ 64 - j + d = (d - j) + 2 ^ 64 by omega_using [hd, hdj], Nat.add_mod_right, Nat.mod_eq_of_lt (a := d - j) (by omega_using [hd])]
    by_cases hdx : d < xs.length
    · rw [ite_eq_left hdx, ite_eq_left hdx, h d hdx]
      by_cases hdy : d - j < ys.length
      · rw [ite_eq_left hdy, ite_eq_left ⟨hdj, by omega_using [hdy]⟩]
      · rw [ite_eq_right hdy, ite_eq_right (by omega_using [hdy])]
    · rw [ite_eq_right hdx, ite_eq_right hdx, ite_eq_right (by omega_using [hy, hdx])]
  · rw [Nat.mod_eq_of_lt (a := 2 ^ 64 - j + d) (by omega_using [hd, hdj]), ite_eq_right (by omega_using [hx, hy])]
    by_cases hdx : d < xs.length
    · rw [ite_eq_left hdx, ite_eq_left hdx, h d hdx, ite_eq_right (by omega_using [hdj])]
    · rw [ite_eq_right hdx, ite_eq_right hdx]

/-- Sixteen more bytes of the key. -/
theorem ipadBlk_add16 (m mk : Mem) (P K : Addr) {B j : Nat} (v : BitVec 128) (hB : B < 2 ^ 63) (hj : j + 16 ≤ B)
    (hv : vbytes v = (bytesAt mk (K + BitVec.ofNat 64 j) 16).map (· ^^^ ipad)) :
    (writeBytes m P (ipadBlk mk K B j)).writeW (P + BitVec.ofNat 64 j) v = writeBytes m P (ipadBlk mk K B (j + 16)) := by
  obtain hl : ((bytesAt mk (K + BitVec.ofNat 64 j) 16).map (· ^^^ ipad)).length = 16 := by
    rw [List.length_map, bytesAt_length]
  rw [store16, hv]
  refine writeBytes_over _ _ _ _ _ (by rw [ipadBlk_length]; exact hB) (by rw [ipadBlk_length, hl]; exact hj)
    (by rw [ipadBlk_length, ipadBlk_length]) fun i hi => ?_
  rw [ipadBlk_length] at hi
  rw [hl]
  simp only [ipadBlk, bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
    Option.map_some, Option.getD_some]
  by_cases hi' : j ≤ i ∧ i < j + 16
  · rw [ite_eq_left hi', List.getElem?_range (by omega_using [hi']), ite_eq_left hi'.2]
    simp only [Option.map_some, Option.getD_some]
    rw [add_ofNat, show j + (i - j) = i by omega_using [hi']]
  · rw [ite_eq_right hi']
    by_cases hij : i < j
    · rw [ite_eq_left hij, ite_eq_left (by omega_using [hij])]
    · rw [ite_eq_right hij, ite_eq_right (by omega_using [hi', hij])]

/-- One more 16 bytes of the outer buffer, after `16 n` of them: the inner
buffer's, XORed with `0x6a` in every byte. -/
theorem xorOpad_mem16 (m : Mem) (A Q : Addr) (n : Nat) (c : BitVec 128) (hc : vbytes c = List.replicate 16 (0x6a : Byte))
    (hsep : Mem.Sep A (16 * n + 16) Q (16 * n + 16)) (hlt : 16 * n + 16 < 2 ^ 64) :
    (writeBytes m Q ((bytesAt m A (16 * n)).map (· ^^^ 0x6a))).writeW (Q + BitVec.ofNat 64 (16 * n))
      ((writeBytes m Q ((bytesAt m A (16 * n)).map (· ^^^ 0x6a))).readW (A + BitVec.ofNat 64 (16 * n)) 128 ^^^ c) =
      writeBytes m Q ((bytesAt m A (16 * n + 16)).map (· ^^^ 0x6a)) := by
  obtain hl : ((bytesAt m A (16 * n)).map (· ^^^ (0x6a : Byte))).length = 16 * n := by
    rw [List.length_map, bytesAt_length]
  rw [store16, vbytes_xor _ _ _ hc, vbytes_readW, bytesAt_writeBytes_sep]
  · rw [bytesAt_add, List.map_append]
    exact Pbkdf2.Memory.writeBytes_append' _ _ _ (by rw [hl])
      (by rw [hl, List.length_map, bytesAt_length]; exact hlt)
  · intro x hx hy
    rw [hl] at hy
    apply hsep x _ (by omega_using [hy])
    rw [show x - A = (x - (A + BitVec.ofNat 64 (16 * n))) + BitVec.ofNat 64 (16 * n) by
        rw [← BitVec.sub_sub, BitVec.sub_add_cancel],
      BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 * n) (by omega_using [hlt])]
    have := Nat.mod_le ((x - (A + BitVec.ofNat 64 (16 * n))).toNat + 16 * n) (2 ^ 64)
    omega_using [hx]
  · omega_using []

theorem mask64 : ∀ j < 4, BitVec.ofNat 64 (16 * j) &&& (BitVec.ofNat 32 (64 - 16)).signExtend 64 =
    BitVec.ofNat 64 (16 * j) := by decide

theorem mask128 : ∀ j < 8, BitVec.ofNat 64 (16 * j) &&& (BitVec.ofNat 32 (128 - 16)).signExtend 64 =
    BitVec.ofNat 64 (16 * j) := by decide

/-- The 16-byte key loop's index, clamped to the block, is itself. -/
theorem and_mask16 {B : Nat} (hB : B = 64 ∨ B = 128) {j : Nat} (hj : 16 * j + 16 ≤ B) :
    BitVec.ofNat 64 (16 * j) &&& (BitVec.ofNat 32 (B - 16)).signExtend 64 = BitVec.ofNat 64 (16 * j) := by
  rcases hB with rfl | rfl
  · exact mask64 j (by omega_using [hj])
  · exact mask128 j (by omega_using [hj])

theorem shr4 (x : BitVec 64) : x >>> 4 = BitVec.ofNat 64 (x.toNat / 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt (by have := x.isLt; omega_using [])]

theorem ea_keyAt (s : State) : s.ea H.keyAt = s.gpr .rbx + BitVec.ofNat 64 H.P.N + s.gpr .r10 := by
  simp only [State.ea, Hash.keyAt, ofInt_natCast, show BitVec.ofNat 64 1 = 1 from rfl]
  ac_rfl

/-! The instructions of the key setup, with what they keep of the SSE
registers. -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_movX {d r : Reg} (k : ∀ s', Upd s s' d (s.gpr r) → s'.xmm = s.xmm → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (.reg r) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _) rfl)

theorem wp_mov32iX {d : Reg} {v : BitVec 32}
    (k : ∀ s', Upd s s' d (v.setWidth 64) → s'.xmm = s.xmm → WP isa (.block is) s' Q) :
    WP isa (.block (.mov32 d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _) rfl)

theorem wp_andiX {d : Reg} {v : BitVec 32}
    (k : ∀ s', Upd s s' d (s.gpr d &&& v.signExtend 64) → s'.xmm = s.xmm → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .and d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _) rfl)

theorem wp_addiX {d : Reg} {v : BitVec 32}
    (k : ∀ s', Upd s s' d (s.gpr d + v.signExtend 64) → s'.xmm = s.xmm → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .add d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _) rfl)

theorem wp_subiX {d : Reg} {v : BitVec 32}
    (k : ∀ s', Upd s s' d (s.gpr d - v.signExtend 64) → s'.xmm = s.xmm →
      s'.zf = some (s.gpr d - v.signExtend 64 == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .sub d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _) rfl rfl)

/-- Sixteen bytes loaded into `d` and XORed with `c`. -/
theorem wp_loadXor {d c : XReg} {m : MemOp} {a : Addr} (hdc : ¬c = d) (ha : s.ea m = a)
    (hin : InRegions (s.rd ++ s.wr) a 16)
    (k : ∀ s', s'.gpr = s.gpr → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      s'.xmm d = s.mem.readW a 128 ^^^ s.xmm c → (∀ y, ¬y = d → s'.xmm y = s.xmm y) → WP isa (.block is) s' Q) :
    WP isa (.block (.movdquLoad d m :: .xop (.bin .pxor d c) :: is)) s Q := by
  refine WP.cons (s' := s.setXmm d (s.mem.readW a 128)) (by simp [exec, State.load128, ha, hin])
    (wp_xbin (k _ rfl rfl rfl rfl ?_ fun y hy => ?_))
  · rw [RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_of_ne _ _ hdc]; rfl
  · rw [RegUpd.xmm_setXmm_of_ne _ _ hy, RegUpd.xmm_setXmm_of_ne _ _ hy]

/-- `Hash.padConst`: `c` in both halves of `x`, through `rax`. -/
theorem padConst_ok {x : XReg} {c : BitVec 64} {rest : List Instr}
    (k : ∀ s', (∀ r, ¬r = .rax → s'.gpr r = s.gpr r) → s'.xmm x = rep16 c →
      (∀ y, ¬y = x → s'.xmm y = s.xmm y) → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      WP isa (.block rest) s' Q) :
    WP isa (.block (Hash.padConst x c ++ rest)) s Q := by
  simp only [Hash.padConst, List.cons_append, List.nil_append]
  refine wp_movImm64' (wp_movqx (wp_xbin (k _ (fun r h => ?_) ?_ (fun y h => ?_) rfl rfl rfl)))
  · rw [RegUpd.gpr_setXmm, RegUpd.gpr_setXmm, RegUpd.gpr_setReg_of_ne _ _ h]
  · rw [RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_self, RegUpd.gpr_setReg_self]; rfl
  · rw [RegUpd.xmm_setXmm_of_ne _ _ h, RegUpd.xmm_setXmm_of_ne _ _ h]; rfl

end

/-- Stores of `xmm0`, `ipad` in every byte, at `rbx + o + 16 k`, for `k < n`,
which write `16 n` bytes of `ipad` from `p = rbx + o`. -/
theorem fill_ok {o : Nat} {p : Addr} : ∀ n (rest : List Instr) (s : State) (Q : State → Prop),
    s.gpr .rbx + BitVec.ofNat 64 o = p → vbytes (s.xmm .xmm0) = List.replicate 16 ipad →
    (∀ k < n, InRegions s.wr (p + BitVec.ofNat 64 (16 * k)) 16) → 16 * n + 16 < 2 ^ 64 →
    (∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr → s'.xmm = s.xmm →
      s'.mem = writeBytes s.mem p (List.replicate (16 * n) ipad) → WP isa (.block rest) s' Q) →
    WP isa (.block ((List.range n).map (fun k => Instr.movdquStore (at_ .rbx (o + 16 * k)) .xmm0) ++ rest)) s Q := by
  intro n
  induction n with
  | zero =>
    intro rest s Q _ _ _ _ k
    exact k s rfl rfl rfl rfl (by simp [writeBytes_nil])
  | succ n ih =>
    intro rest s Q hp hx hout hn k
    rw [List.range_succ, List.map_append, List.map_singleton, List.append_assoc]
    refine ih _ s Q hp hx (fun j hj => hout j (by omega_using [hj])) (by omega_using [hn]) fun s₁ g₁ rd₁ wr₁ x₁ m₁ => ?_
    simp only [List.cons_append, List.nil_append]
    refine wp_movdquStoreX (a := p + BitVec.ofNat 64 (16 * n)) (by rw [ea_off, g₁, hp])
      (by rw [wr₁]; exact hout n (by omega_using [])) fun s₂ g₂ m₂ rd₂ wr₂ x₂ =>
        k s₂ (by rw [g₂, g₁]) (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁]) (by rw [x₂, x₁]) ?_
    rw [m₂, m₁, x₁, store16, hx,
      Pbkdf2.Memory.writeBytes_append' _ _ _ (by rw [List.length_replicate])
        (by simp only [List.length_replicate]; omega_using [hn]),
      List.replicate_append_replicate, Nat.mul_succ]

/-- After `j` bytes of the key at `K` (whose bytes are those of `mk`), from the
state `s` the loops start in: the buffer at `P` holds `ipadBlk … j` over `m`. -/
structure KeyInv (s : State) (m mk : Mem) (P K : Addr) (B j : Nat) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  other : ∀ r, r ≠ .rax → r ≠ .r14 → r ≠ .r10 → r ≠ .rcx → t.gpr r = s.gpr r
  r14 : t.gpr .r14 = BitVec.ofNat 64 j
  mem : t.mem = writeBytes m P (ipadBlk mk K B j)

/-- Where the key loops read and write. -/
structure KeyRegs (H : Hash) (s : State) (m mk : Mem) (P K : Addr) (kl : Nat) : Prop where
  kl_le : kl ≤ H.P.B
  hB : H.P.B = 64 ∨ H.P.B = 128
  rbp : s.gpr .rbp = K
  rbx : s.gpr .rbx + BitVec.ofNat 64 H.P.N = P
  r13 : s.gpr .r13 = BitVec.ofNat 64 kl
  key : ∀ i < kl, m (K + BitVec.ofNat 64 i) = mk (K + BitVec.ofNat 64 i)
  kin : ∀ i n, i + n ≤ kl → InRegions (s.rd ++ s.wr) (K + BitVec.ofNat 64 i) n
  bout : ∀ i n, i + n ≤ H.P.B → InRegions s.wr (P + BitVec.ofNat 64 i) n
  disj : Region.Disjoint ⟨K, kl⟩ ⟨P, H.P.B⟩

/-- The key's bytes are still where they were. -/
theorem KeyInv.key {s : State} {m mk : Mem} {P K : Addr} {kl : Nat} (hr : KeyRegs H s m mk P K kl) {j : Nat}
    {t : State} (h : KeyInv s m mk P K H.P.B j t) {i : Nat} (hi : i < kl) :
    t.mem (K + BitVec.ofNat 64 i) = mk (K + BitVec.ofNat 64 i) := by
  have hkl := hr.kl_le
  obtain hB : H.P.B ≤ 128 := by rcases hr.hB with h | h <;> omega_using [h]
  obtain hl : (ipadBlk mk K H.P.B j).length = H.P.B := ipadBlk_length _ _ _ _
  rw [h.mem, ← hr.key i hi]
  refine (writeBytes_frame m P _ (R := ⟨P, H.P.B⟩) (by rw [hl]; exact Region.contains_self _ _)).bytes
    (R := ⟨K, kl⟩) ?_ (by show kl ≤ 2 ^ 64; omega_using [hkl, hB]) hi
  simp only [List.mem_singleton]; rintro r rfl; exact hr.disj

theorem key_step16 {s : State} {m mk : Mem} {P K : Addr} {kl : Nat} (hr : KeyRegs H s m mk P K kl)
    (hx0 : vbytes (s.xmm .xmm0) = List.replicate 16 ipad) {j : Nat} (hj : j < kl / 16) {t : State}
    (h : KeyInv s m mk P K H.P.B (16 * j) t) (hx : t.xmm .xmm0 = s.xmm .xmm0)
    (hc : t.gpr .rcx = BitVec.ofNat 64 (kl / 16 - j)) :
    WP isa (.block [.movdquLoad .xmm1 (byteAt .rbp 0), .xop (.bin .pxor .xmm1 .xmm0),
      .mov .r10 (.reg .r14), .alu .and .r10 (.imm (BitVec.ofNat 32 (H.P.B - 16))),
      .movdquStore H.keyAt .xmm1, .alu .add .r14 (.imm 16), .alu .sub .rcx (.imm 1)]) t
      fun t' => (KeyInv s m mk P K H.P.B (16 * (j + 1)) t' ∧ t'.xmm .xmm0 = s.xmm .xmm0 ∧
        t'.gpr .rcx = BitVec.ofNat 64 (kl / 16 - (j + 1))) ∧ t'.zf = some (decide (j + 1 = kl / 16)) := by
  have hkl := hr.kl_le
  obtain hB : H.P.B ≤ 128 := by rcases hr.hB with h | h <;> omega_using [h]
  obtain hj16 : 16 * j + 16 ≤ kl := by omega_using [hj]
  refine wp_loadXor (a := K + BitVec.ofNat 64 (16 * j)) (by decide)
    (by rw [ea_byteAt _ _ _ _ h.r14, h.other _ (by decide) (by decide) (by decide) (by decide), hr.rbp,
      BitVec.add_zero])
    (by rw [h.rd, h.wr]; exact hr.kin _ 16 hj16) fun t₀ g₀ m₀ rd₀ wr₀ x₀ xo₀ => ?_
  refine wp_movX fun t₁ u₁ x₁ => wp_andiX fun t₂ u₂ x₂ => ?_
  obtain h10 : t₂.gpr .r10 = BitVec.ofNat 64 (16 * j) := by
    rw [u₂.gpr, u₁.gpr, g₀, h.r14, and_mask16 hr.hB (by omega_using [hj, hkl])]
  refine wp_movdquStoreX (a := P + BitVec.ofNat 64 (16 * j))
    (by rw [ea_keyAt, h10, u₂.other _ (by decide), u₁.other _ (by decide), g₀,
      h.other _ (by decide) (by decide) (by decide) (by decide), hr.rbx])
    (by rw [u₂.wr, u₁.wr, wr₀, h.wr]; exact hr.bout _ 16 (by omega_using [hj, hkl])) fun t₃ g₃ m₃ rd₃ wr₃ x₃ => ?_
  refine wp_addiX fun t₄ u₄ x₄ => wp_subiX fun t₅ u₅ x₅ z₅ => WP.block_nil ?_
  obtain hv : vbytes (t.mem.readW (K + BitVec.ofNat 64 (16 * j)) 128 ^^^ t.xmm .xmm0) =
      (bytesAt mk (K + BitVec.ofNat 64 (16 * j)) 16).map (· ^^^ ipad) := by
    rw [vbytes_xor _ _ _ (by rw [hx]; exact hx0), vbytes_readW]
    congr 1
    simp only [bytesAt]
    refine List.map_congr_left fun i hi => ?_
    obtain hi := List.mem_range.mp hi
    rw [add_ofNat]
    exact h.key hr (by omega_using [hj, hi])
  obtain c₄ : t₄.gpr .rcx = BitVec.ofNat 64 (kl / 16 - j) := by
    rw [u₄.other _ (by decide), g₃, u₂.other _ (by decide), u₁.other _ (by decide), g₀, hc]
  refine ⟨⟨⟨by rw [u₅.rd, u₄.rd, rd₃, u₂.rd, u₁.rd, rd₀, h.rd], by rw [u₅.wr, u₄.wr, wr₃, u₂.wr, u₁.wr, wr₀, h.wr],
    fun r h1 h2 h3 h4 => by
      rw [u₅.other r h4, u₄.other r h2, g₃, u₂.other r h3, u₁.other r h3, g₀, h.other r h1 h2 h3 h4],
    by rw [u₅.other _ (by decide), u₄.gpr, g₃, u₂.other _ (by decide), u₁.other _ (by decide), g₀, h.r14,
      show (16 : BitVec 32).signExtend 64 = BitVec.ofNat 64 16 from rfl, ← BitVec.ofNat_add, Nat.mul_succ], ?_⟩,
    by rw [x₅, x₄, x₃, x₂, x₁, xo₀ _ (by decide), hx], ?_⟩, ?_⟩
  · rw [u₅.mem, u₄.mem, m₃, x₂, x₁, x₀, u₂.mem, u₁.mem, m₀]
    generalize t.mem.readW (K + BitVec.ofNat 64 (16 * j)) 128 ^^^ t.xmm .xmm0 = v at hv ⊢
    rw [h.mem, ipadBlk_add16 _ _ _ _ _ (by omega_using [hB]) (by omega_using [hj, hkl]) hv, Nat.mul_succ]
  · rw [u₅.gpr, c₄, sx_one, ofNat_pred (by omega_using [hj])]; rfl
  · rw [z₅, c₄, sx_one, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, sub_beq (by omega_using [hkl, hB]) (by omega_using [])]
    exact congrArg some (decide_eq_decide.mpr (by omega_using []))

/-- The 16-byte key loop, skipped for a key shorter than that. -/
theorem key16_ok {s : State} {m mk : Mem} {P K : Addr} {kl : Nat} (hr : KeyRegs H s m mk P K kl)
    (hx0 : vbytes (s.xmm .xmm0) = List.replicate 16 ipad) (h14 : s.gpr .r14 = BitVec.ofNat 64 0)
    (hc : s.gpr .rcx = BitVec.ofNat 64 (kl / 16)) (hz : s.zf = some (decide (kl / 16 = 0)))
    (hm : s.mem = writeBytes m P (ipadBlk mk K H.P.B 0)) :
    WP isa (.ite .e (.block []) H.keyLoop16) s (KeyInv s m mk P K H.P.B (16 * (kl / 16))) := by
  obtain i0 : KeyInv s m mk P K H.P.B (16 * 0) s := ⟨rfl, rfl, fun _ _ _ _ _ => rfl, h14, hm⟩
  refine WP.ite (decide (kl / 16 = 0)) (by simp [eval, hz]) (fun h0 => WP.block_nil ?_) fun h0 => ?_
  · have : kl / 16 = 0 := by simpa using h0
    rw [this]; exact i0
  · have : 0 < kl / 16 := by simp at h0; omega_using [h0]
    exact WP.mono (count_loop this
      (fun j t => KeyInv s m mk P K H.P.B (16 * j) t ∧ t.xmm .xmm0 = s.xmm .xmm0 ∧
        t.gpr .rcx = BitVec.ofNat 64 (kl / 16 - j))
      (fun j hj t h => key_step16 hr hx0 hj h.1 h.2.1 h.2.2) ⟨i0, rfl, hc⟩) fun t ht => ht.1

theorem key_step {s : State} {m mk : Mem} {P K : Addr} {kl : Nat} (hr : KeyRegs H s m mk P K kl) {j : Nat}
    (hj : j < kl) {t : State} (h : KeyInv s m mk P K H.P.B j t) :
    WP isa (.block [.movzx8 .rax (byteAt .rbp 0), .alu32 .xor .rax (.imm 0x36),
      .mov .r10 (.reg .r14), .alu .and .r10 (.imm (BitVec.ofNat 32 (H.P.B - 1))),
      .store8 H.keyAt .rax, .alu .add .r14 (.imm 1), .alu .cmp .r14 (.reg .r13)]) t
      fun t' => KeyInv s m mk P K H.P.B (j + 1) t' ∧ t'.zf = some (decide (j + 1 = kl)) := by
  have hkl := hr.kl_le
  obtain hB : H.P.B ≤ 128 := by rcases hr.hB with h | h <;> omega_using [h]
  obtain hl : (ipadBlk mk K H.P.B j).length = H.P.B := ipadBlk_length _ _ _ _
  obtain hbyte : t.mem (K + BitVec.ofNat 64 j) = mk (K + BitVec.ofNat 64 j) := h.key hr hj
  refine wp_movzx8 (a := K + BitVec.ofNat 64 j)
    (by rw [ea_byteAt _ _ _ _ h.r14, h.other _ (by decide) (by decide) (by decide) (by decide), hr.rbp,
      BitVec.add_zero])
    (by rw [h.rd, h.wr]; exact hr.kin j 1 hj) fun t₁ u₁ => ?_
  refine wp_xor32i fun t₂ u₂ => wp_mov fun t₃ u₃ _ _ => wp_andi fun t₄ u₄ => ?_
  obtain h10 : t₄.gpr .r10 = BitVec.ofNat 64 j := by
    rw [u₄.gpr, u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h.r14, and_mask hr.hB,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := j) (by omega_using [hj, hkl, hB]),
      Nat.mod_eq_of_lt (by omega_using [hj, hkl])]
  refine wp_store8 (a := P + BitVec.ofNat 64 j)
    (by rw [ea_keyAt, h10, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), h.other _ (by decide) (by decide) (by decide) (by decide), hr.rbx])
    (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr]; exact hr.bout j 1 (by omega_using [hj, hkl]))
    fun t₅ g₅ m₅ rd₅ wr₅ => ?_
  refine wp_addi fun t₆ u₆ => wp_cmp fun t₇ g₇ m₇ rd₇ wr₇ _ z₇ => WP.block_nil ?_
  obtain h14 : t₆.gpr .r14 = BitVec.ofNat 64 (j + 1) := by
    rw [u₆.gpr, g₅, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), h.r14, sx_one, ofNat_succ]
  refine ⟨⟨by rw [rd₇, u₆.rd, rd₅, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd],
    by rw [wr₇, u₆.wr, wr₅, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr],
    fun r h1 h2 h3 h4 => by
      rw [g₇, u₆.other r h2, g₅, u₄.other r h3, u₃.other r h3, u₂.other r h1, u₁.other r h1,
        h.other r h1 h2 h3 h4],
    by rw [g₇, h14], ?_⟩, ?_⟩
  · have v : (t₄.gpr .rax).setWidth 8 = mk (K + BitVec.ofNat 64 j) ^^^ ipad := by
      rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.gpr, xor_byte, hbyte]; rfl
    rw [m₇, u₆.mem, m₅, v, u₄.mem, u₃.mem, u₂.mem, u₁.mem, h.mem,
      writeBytes_set _ _ _ (by rw [hl]; omega_using [hj, hkl]) (by rw [hl]; omega_using [hB]), ipadBlk_succ]
  · rw [z₇, h14, show t₆.gpr .r13 = BitVec.ofNat 64 kl by
      rw [u₆.other _ (by decide), g₅, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
        u₁.other _ (by decide), h.other _ (by decide) (by decide) (by decide) (by decide), hr.r13],
      sub_beq (by omega_using [hj, hkl, hB]) (by omega_using [hkl, hB])]

/-- The byte loop over the rest of the key, skipped when there is none. -/
theorem key_ok {s : State} {m mk : Mem} {P K : Addr} {kl : Nat} (hr : KeyRegs H s m mk P K kl) {j₀ : Nat}
    (hj₀ : j₀ ≤ kl) {t : State} (h : KeyInv s m mk P K H.P.B j₀ t) (hz : t.zf = some (decide (j₀ = kl))) :
    WP isa (.ite .e (.block []) H.keyLoop) t (KeyInv s m mk P K H.P.B kl) := by
  refine WP.ite (decide (j₀ = kl)) (by simp [eval, hz]) (fun h0 => WP.block_nil ?_) fun h0 => ?_
  · have : j₀ = kl := by simpa using h0
    rw [← this]; exact h
  · have hlt : 0 < kl - j₀ := by simp at h0; omega_using [h0, hj₀]
    obtain e : j₀ + (kl - j₀) = kl := by omega_using [hj₀]
    have := count_loop hlt (fun k t => KeyInv s m mk P K H.P.B (j₀ + k) t)
      (fun k hk t h => WP.mono (key_step hr (j := j₀ + k) (by omega_using [hk, hj₀]) h) fun t' ht' =>
        ⟨ht'.1, by rw [ht'.2]; exact congrArg some (decide_eq_decide.mpr (by omega_using [hk, hj₀]))⟩) h
    rwa [e] at this

/-- The 16-byte words of the outer buffer: `n` words of the inner buffer at
`rbx + N`, XORed with `xmm1`, `ipad ⊕ opad` in every byte, to `r12 + N`. -/
theorem opad_ok : ∀ n (rest : List Instr) (s : State) (Q : State → Prop),
    vbytes (s.xmm .xmm1) = List.replicate 16 (0x6a : Byte) →
    (∀ k < n, InRegions (s.rd ++ s.wr) (s.gpr .rbx + BitVec.ofNat 64 H.P.N + BitVec.ofNat 64 (16 * k)) 16) →
    (∀ k < n, InRegions s.wr (s.gpr .r12 + BitVec.ofNat 64 H.P.N + BitVec.ofNat 64 (16 * k)) 16) →
    Mem.Sep (s.gpr .rbx + BitVec.ofNat 64 H.P.N) (16 * n) (s.gpr .r12 + BitVec.ofNat 64 H.P.N) (16 * n) →
    16 * n < 2 ^ 64 →
    (∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr → s'.xmm .xmm1 = s.xmm .xmm1 →
      s'.mem = writeBytes s.mem (s.gpr .r12 + BitVec.ofNat 64 H.P.N)
        ((bytesAt s.mem (s.gpr .rbx + BitVec.ofNat 64 H.P.N) (16 * n)).map (· ^^^ 0x6a)) →
      WP isa (.block rest) s' Q) →
    WP isa (.block ((List.range n).flatMap H.opadW ++ rest)) s Q := by
  intro n
  induction n with
  | zero =>
    intro rest s Q _ _ _ _ _ k
    exact k s rfl rfl rfl rfl (by simp [bytesAt, writeBytes_nil])
  | succ n ih =>
    intro rest s Q hx hin hout hsep hlt k
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    refine ih _ s Q hx (fun j hj => hin j (by omega_using [hj])) (fun j hj => hout j (by omega_using [hj]))
      (fun x hx hy => hsep x (by omega_using [hx]) (by omega_using [hy])) (by omega_using [hlt])
      fun s₁ g₁ rd₁ wr₁ x₁ m₁ => ?_
    simp only [Hash.opadW, List.cons_append, List.nil_append]
    refine wp_loadXor (a := s.gpr .rbx + BitVec.ofNat 64 H.P.N + BitVec.ofNat 64 (16 * n)) (by decide)
      (by rw [ea_off, g₁]) (by rw [rd₁, wr₁]; exact hin n (by omega_using [])) fun s₂ g₂ m₂ rd₂ wr₂ x₂ xo₂ => ?_
    refine wp_movdquStoreX (a := s.gpr .r12 + BitVec.ofNat 64 H.P.N + BitVec.ofNat 64 (16 * n))
      (by rw [ea_off, g₂, g₁]) (by rw [wr₂, wr₁]; exact hout n (by omega_using []))
      fun s₃ g₃ m₃ rd₃ wr₃ x₃ => k s₃ (by rw [g₃, g₂, g₁]) (by rw [rd₃, rd₂, rd₁]) (by rw [wr₃, wr₂, wr₁])
        (by rw [x₃, xo₂ _ (by decide), x₁]) ?_
    rw [m₃, x₂, m₂, m₁, x₁, Nat.mul_succ,
      xorOpad_mem16 _ _ _ _ _ hx (by rwa [← Nat.mul_succ]) (by omega_using [hlt])]

section
variable {sc : Nat} {s₀ : State} (hp : Pre H sc s₀)
include hH hp

/-- `K₀ ⊕ ipad` into the inner buffer and `K₀ ⊕ opad` into the outer one, and
the inner block's address in `rsi`. -/
theorem keys_ok {s : State} (hk : KR H s₀ (inn s₀) s) :
    WP isa H.initKeys s fun t => KR H s₀ (inn s₀) t ∧ t.gpr .rsi = bufOf H (inn s₀) ∧
      Frame [⟨bufOf H (inn s₀), H.P.B⟩, ⟨bufOf H (out s₀), H.P.B⟩] s.mem t.mem ∧
      bytesAt t.mem (bufOf H (inn s₀)) H.P.B = xorPad (k0 H s₀) ipad ∧
      bytesAt t.mem (bufOf H (out s₀)) H.P.B = xorPad (k0 H s₀) opad := by
  obtain ⟨hN4, hB4, hN, hB0, hB, -⟩ := sizes hH hp
  have hkl := hp.kl_le
  have hd := hH.dims.B
  obtain eB : 16 * (H.P.B / 16) = H.P.B := by rcases hd with h | h <;> omega_using [h]
  obtain si := stOk_in (H := H) hp
  obtain so := stOk_out (H := H) hp
  obtain bI : Region.Sub ⟨bufOf H (inn s₀), H.P.B⟩ ⟨inn s₀, H.S⟩ := Offset.sub_base _ (Nat.le_refl _)
  obtain bO : Region.Sub ⟨bufOf H (out s₀), H.P.B⟩ ⟨out s₀, H.S⟩ := Offset.sub_base _ (Nat.le_refl _)
  have hS : H.S = H.P.N + H.P.B := rfl
  obtain inI : ∀ i n, i + n ≤ H.P.B → InRegions s₀.wr (bufOf H (inn s₀) + BitVec.ofNat 64 i) n :=
    fun i n hn => ⟨_, si.mem, by rw [add_ofNat]; exact Offset.contains_base _ (by omega_using [hS, hn]) (by omega_using [hN, hB, hn])⟩
  obtain inO : ∀ i n, i + n ≤ H.P.B → InRegions s₀.wr (bufOf H (out s₀) + BitVec.ofNat 64 i) n :=
    fun i n hn => ⟨_, so.mem, by rw [add_ofNat]; exact Offset.contains_base _ (by omega_using [hS, hn]) (by omega_using [hN, hB, hn])⟩
  obtain dIO : Region.Disjoint ⟨bufOf H (inn s₀), H.P.B⟩ ⟨bufOf H (out s₀), H.P.B⟩ :=
    (hp.i_o.sub_left bI).sub_right bO
  unfold Hash.initKeys Hash.ipadFill
  rw [List.append_assoc]
  refine WP.seq (padConst_ok fun s₁ g₁ x₁ xo₁ m₁ rd₁ wr₁ => ?_)
  refine fill_ok (o := H.P.N) (p := bufOf H (inn s₀)) (H.P.B / 16) _ s₁ _ (by rw [g₁ _ (by decide), hk.rbx])
    (by rw [x₁]; exact vbytes_ipad) (fun k hk' => by rw [wr₁, hk.wr]; exact inI _ 16 (by omega_using [hk', eB]))
    (by omega_using [hB]) fun s₂ g₂ rd₂ wr₂ x₂ m₂ => ?_
  refine wp_mov32iX fun s₃ u₃ x₃ => wp_movX fun s₄ u₄ x₄ => wp_shrX (by decide) fun s₆ u₅ x₆ =>
    wp_testX fun s₅ g₆ m₆ rd₆ wr₆ xt₆ z₅ => WP.block_nil ?_
  obtain G₅ : ∀ r, r ≠ .rax → r ≠ .r14 → r ≠ .rcx → s₅.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [g₆, u₅.other r h3, u₄.other r h3, u₃.other r h2, g₂, g₁ r h1]
  obtain rd₅ : s₅.rd = s₀.rd := by rw [rd₆, u₅.rd, u₄.rd, u₃.rd, rd₂, rd₁, hk.rd]
  obtain wr₅ : s₅.wr = s₀.wr := by rw [wr₆, u₅.wr, u₄.wr, u₃.wr, wr₂, wr₁, hk.wr]
  obtain r13₄ : s₃.gpr .r13 = s₀.gpr .rcx := by
    rw [u₃.other _ (by decide), g₂, g₁ _ (by decide), hk.r13]
  obtain hr : KeyRegs H s₅ s.mem s₀.mem (bufOf H (inn s₀)) (kp s₀) (kl s₀) :=
    { kl_le := hkl, hB := hd
      rbp := by rw [G₅ _ (by decide) (by decide) (by decide), hk.rbp]
      rbx := by rw [G₅ _ (by decide) (by decide) (by decide), hk.rbx]
      r13 := by rw [G₅ _ (by decide) (by decide) (by decide), hk.r13, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      key := hk.key
      kin := fun i n hi => by
        rw [rd₅, wr₅, hp.rd]
        exact ⟨_, List.mem_append_left _ (List.mem_singleton_self _),
          Offset.contains_base _ (by omega_using [hi]) (by omega_using [hB, hkl, hi])⟩
      bout := fun i n hi => by rw [wr₅]; exact inI i n hi
      disj := hp.k_i.sub_right bI }
  obtain hx0 : vbytes (s₅.xmm .xmm0) = List.replicate 16 ipad := by
    rw [xt₆, x₆, x₄, x₃, x₂, x₁]; exact vbytes_ipad
  obtain h14 : s₅.gpr .r14 = BitVec.ofNat 64 0 := by rw [g₆, u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr]; rfl
  obtain hc : s₅.gpr .rcx = BitVec.ofNat 64 (kl s₀ / 16) := by rw [g₆, u₅.gpr, u₄.gpr, r13₄, shr4]
  obtain hz : s₅.zf = some (decide (kl s₀ / 16 = 0)) := by
    rw [z₅, BitVec.and_self, u₅.gpr, u₄.gpr, r13₄, shr4, ofNat_beq_zero (by omega_using [hkl, hB])]
  obtain hm : s₅.mem = writeBytes s.mem (bufOf H (inn s₀)) (ipadBlk s₀.mem (kp s₀) H.P.B 0) := by
    rw [m₆, u₅.mem, u₄.mem, u₃.mem, m₂, m₁, ipadBlk_zero, eB]
  refine WP.seq (WP.mono (key16_ok hr hx0 h14 hc hz hm) fun t₆ h₆ => ?_)
  refine WP.seq (wp_cmp fun t₇ g₇ m₇ rd₇ wr₇ _ z₇ => WP.block_nil ?_)
  obtain h₇ : KeyInv s₅ s.mem s₀.mem (bufOf H (inn s₀)) (kp s₀) H.P.B (16 * (kl s₀ / 16)) t₇ :=
    ⟨by rw [rd₇, h₆.rd], by rw [wr₇, h₆.wr], fun r h1 h2 h3 h4 => by rw [g₇, h₆.other r h1 h2 h3 h4],
      by rw [g₇, h₆.r14], by rw [m₇, h₆.mem]⟩
  obtain hz₇ : t₇.zf = some (decide (16 * (kl s₀ / 16) = kl s₀)) := by
    rw [z₇, h₆.r14, h₆.other _ (by decide) (by decide) (by decide) (by decide), hr.r13,
      sub_beq (by omega_using [hkl, hB]) (by omega_using [hkl, hB])]
  refine WP.seq (WP.mono (key_ok hr (by omega_using []) h₇ hz₇) fun t ht => ?_)
  obtain Gt : ∀ r, r ≠ .rax → r ≠ .r14 → r ≠ .r10 → r ≠ .rcx → t.gpr r = s.gpr r := fun r h1 h2 h3 h4 => by
    rw [ht.other r h1 h2 h3 h4, G₅ r h1 h2 h4]
  obtain bxt : t.gpr .rbx = inn s₀ := by rw [Gt _ (by decide) (by decide) (by decide) (by decide), hk.rbx]
  obtain r12t : t.gpr .r12 = out s₀ := by rw [Gt _ (by decide) (by decide) (by decide) (by decide), hk.r12]
  obtain rdt : t.rd = s₀.rd := by rw [ht.rd, rd₅]
  obtain wrt : t.wr = s₀.wr := by rw [ht.wr, wr₅]
  unfold Hash.opadFill
  rw [List.append_assoc]
  refine padConst_ok fun s₈ g₈ x₈ xo₈ m₈ rd₈ wr₈ => ?_
  obtain bx₈ : s₈.gpr .rbx = inn s₀ := by rw [g₈ _ (by decide), bxt]
  obtain r12₈ : s₈.gpr .r12 = out s₀ := by rw [g₈ _ (by decide), r12t]
  refine opad_ok (H.P.B / 16) _ s₈ _ (by rw [x₈]; exact vbytes_x6a)
    (fun k hk' => by rw [bx₈, rd₈, wr₈, rdt, wrt]; exact InRegions.right' (inI _ 16 (by omega_using [hk', eB])))
    (fun k hk' => by rw [r12₈, wr₈, wrt]; exact inO _ 16 (by omega_using [hk', eB]))
    (by rw [bx₈, r12₈, eB]; exact dIO.sep (Region.contains_self _ _) (Region.contains_self _ _)) (by omega_using [hB])
    fun s₉ g₉ rd₉ wr₉ _ m₉ => ?_
  refine wp_mov fun s₁₀ u₁₀ _ _ => wp_addi fun s₁₁ u₁₁ => WP.block_nil ?_
  rw [bx₈, r12₈, eB, m₈] at m₉
  obtain G : ∀ r, r ≠ .rax → r ≠ .r14 → r ≠ .r10 → r ≠ .rcx → r ≠ .rsi → s₁₁.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 h5 => by rw [u₁₁.other r h5, u₁₀.other r h5, g₉, g₈ r h1, Gt r h1 h2 h3 h4]
  obtain hm' : s₁₁.mem = s₉.mem := by rw [u₁₁.mem, u₁₀.mem]
  obtain lI : (ipadBlk s₀.mem (kp s₀) H.P.B (kl s₀)).length = H.P.B := ipadBlk_length _ _ _ _
  obtain bt : bytesAt t.mem (bufOf H (inn s₀)) H.P.B = xorPad (k0 H s₀) ipad := by
    rw [ht.mem, bytesAt_writeBytes_self' lI (by omega_using [hB]), ipadBlk_eq _ _ hkl]
  obtain lO : ((bytesAt t.mem (bufOf H (inn s₀)) H.P.B).map (· ^^^ (0x6a : Byte))).length = H.P.B := by
    simp [bytesAt]
  obtain fT : Frame [⟨bufOf H (inn s₀), H.P.B⟩] s.mem t.mem := by
    rw [ht.mem]; exact writeBytes_frame _ _ _ (by rw [lI]; exact Region.contains_self _ _)
  obtain f₉ : Frame [⟨bufOf H (out s₀), H.P.B⟩] t.mem s₉.mem := by
    rw [m₉]; exact writeBytes_frame _ _ _ (by rw [lO]; exact Region.contains_self _ _)
  obtain f : Frame [⟨bufOf H (inn s₀), H.P.B⟩, ⟨bufOf H (out s₀), H.P.B⟩] s.mem s₁₁.mem := by
    rw [hm']; exact (fT.mono (by simp)).trans (f₉.mono (by simp))
  refine ⟨hk.keep (by rw [u₁₁.rd, u₁₀.rd, rd₉, rd₈, rdt, hk.rd]) (by rw [u₁₁.wr, u₁₀.wr, wr₉, wr₈, wrt, hk.wr])
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
          exact G _ (by decide) (by decide) (by decide) (by decide) (by decide)) f
      (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro r (rfl | rfl)
        · exact away_st hH hp si bI
        · exact away_st hH hp so bO),
    by rw [u₁₁.gpr, u₁₀.gpr, g₉, bx₈, sx_ofNat (by omega_using [hN])], f, ?_, ?_⟩
  · have sIO : Mem.Sep (bufOf H (inn s₀)) H.P.B (bufOf H (out s₀))
        ((bytesAt t.mem (bufOf H (inn s₀)) H.P.B).map (· ^^^ (0x6a : Byte))).length := by
      rw [lO]; exact dIO.sep (Region.contains_self _ _) (Region.contains_self _ _)
    rw [hm', m₉, bytesAt_writeBytes_sep _ _ sIO (by omega_using [hB]), bt]
  · rw [hm', m₉, bytesAt_writeBytes_self' lO (by omega_using [hB]), bt, xorOpad_ipad]

/-! ## The compressions -/

/-- What the call of the compression function needs, for the state at `p`. -/
theorem callOk {p : Addr} (hs : StOk (H := H) (sc := sc) (s₀ := s₀) p) {t : State} (hk : KR H s₀ p t)
    (hsi : t.gpr .rsi = bufOf H p) : CallOk H.P t p (scr s₀) (bufOf H p) := by
  obtain ⟨-, -, hN, -, hB, hso, -, -, hL, h8⟩ := sizes hH hp
  obtain sR : scR sc s₀ ∈ s₀.wr := by rw [hp.wr]; simp
  obtain hv : Region.Sub ⟨p, H.P.N⟩ ⟨p, H.S⟩ := Region.sub_prefix (by show H.P.N ≤ H.P.N + H.P.B; omega_using [])
  obtain hb : Region.Sub ⟨bufOf H p, H.P.B⟩ ⟨p, H.S⟩ := Offset.sub_base _ (Nat.le_refl _)
  obtain hc : Region.Sub ⟨scr s₀, H.P.so⟩ (scR sc s₀) := cal_sub hH hp
  obtain b8 : Region.Sub (below (t.gpr .rsp) 8) (stkR s₀) := by
    rw [hk.rsp]; exact Offset.sub_below _ (by omega_using []) (by omega_using [])
  refine ⟨hk.rbx, hk.r15, hsi, (hs.sc.sub_left hv).sub_right hc,
    Offset.disjoint_base _ (Nat.le_refl _) (by omega_using [hN, hB]), (hs.sc.sub_left hb).sub_right hc,
    (hs.stk.sub_left b8).sub_right hv, (hp.stk_s.sub_left b8).sub_right hc,
    (hs.stk.sub_left b8).sub_right hb, ?_, ?_⟩
  · rw [hk.rd, hk.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_append_right _ hs.mem, H.P.N, rfl, by show H.P.N + H.P.B ≤ H.P.N + H.P.B; omega_using []⟩
    · exact ⟨_, List.mem_append_right _ hs.mem, 0, (BitVec.add_zero _).symm,
        by show 0 + H.P.N ≤ H.P.N + H.P.B; omega_using []⟩
    · exact ⟨_, List.mem_append_right _ sR, 0, (BitVec.add_zero _).symm, by show 0 + H.P.so ≤ 8 * sc; omega_using [hso, hL]⟩
  · rw [hk.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, hs.mem, 0, (BitVec.add_zero _).symm, by show 0 + H.P.N ≤ H.P.N + H.P.B; omega_using []⟩
    · exact ⟨_, sR, 0, (BitVec.add_zero _).symm, by show 0 + H.P.so ≤ 8 * sc; omega_using [hso, hL]⟩

/-- The compression of the block in the buffer of the state at `p` into its
hash value. -/
theorem cmp_ok {p : Addr} (hs : StOk (H := H) (sc := sc) (s₀ := s₀) p) {t : State} (hk : KR H s₀ p t)
    (hsi : t.gpr .rsi = bufOf H p) {Q : State → Prop}
    (k : ∀ s', KR H s₀ p s' → Frame [⟨p, H.P.N⟩, calR H s₀, stkR s₀] t.mem s'.mem →
      hH.md.stateAt s'.mem p = hH.md.compress (hH.md.stateAt t.mem p) (hH.md.blockAt t.mem (bufOf H p)) →
      Q s') :
    WP isa (compressAt H.compN H.compC) t Q := by
  obtain ⟨-, -, hN, -, hB, -⟩ := sizes hH hp
  obtain b8 : Region.Sub (below (t.gpr .rsp) 8) (stkR s₀) := by
    rw [hk.rsp]; exact Offset.sub_below _ (by omega_using []) (by omega_using [])
  refine compressAt_ok hH.md hH.comp (callOk hH hp hs hk hsi) (by omega_using [hB]) (by omega_using [hN])
    fun s' hrd hwr hcs hfr hst _ _ => ?_
  obtain f : Frame [⟨p, H.P.N⟩, calR H s₀, stkR s₀] t.mem s'.mem := hfr.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨calR H s₀, by simp, fun _ h => h⟩
    · exact ⟨stkR s₀, by simp, b8⟩
  refine k s' (hk.keep hrd hwr (fun r hr => hcs r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [calleeSaved])) f ?_) f hst
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact away_st hH hp hs (Region.sub_prefix (by show H.P.N ≤ H.P.N + H.P.B; omega_using []))
  · exact away_cal hH hp
  · exact away_stk hH hp (fun _ h => h)

/-- From the inner state to the outer one. -/
theorem mid_ok {s : State} (hk : KR H s₀ (inn s₀) s) :
    WP isa (.block H.initOuter) s fun t => KR H s₀ (out s₀) t ∧ t.gpr .rsi = bufOf H (out s₀) ∧
      t.mem = s.mem := by
  obtain ⟨-, -, hN, -⟩ := sizes hH hp
  unfold Hash.initOuter
  refine wp_mov fun s₁ u₁ _ _ => wp_mov fun s₂ u₂ _ _ => wp_addi fun s₃ u₃ => WP.block_nil ?_
  obtain G : ∀ r, r ≠ .rbx → r ≠ .rsi → s₃.gpr r = s.gpr r := fun r h1 h2 => by
    rw [u₃.other r h2, u₂.other r h2, u₁.other r h1]
  obtain hm : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  refine ⟨⟨by rw [u₃.rd, u₂.rd, u₁.rd, hk.rd], by rw [u₃.wr, u₂.wr, u₁.wr, hk.wr],
    by rw [G _ (by decide) (by decide), hk.rsp],
    by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hk.r12],
    by rw [G _ (by decide) (by decide), hk.rbp], by rw [G _ (by decide) (by decide), hk.r12],
    by rw [G _ (by decide) (by decide), hk.r13], by rw [G _ (by decide) (by decide), hk.r15],
    by rw [hm]; exact hk.saved, by rw [hm]; exact hk.ret, fun i hi => by rw [hm]; exact hk.key i hi⟩,
    by rw [u₃.gpr, u₂.gpr, u₁.other _ (by decide), hk.r12, sx_ofNat (by omega_using [hN])], hm⟩

end

/-- What `init` needs of `H.compBoth`, the code compressing the blocks of
its two states: from the inner state at `rbx` with its block at `rsi`, both
hash values are compressed with the blocks in their buffers, and what the
prologue set up is kept (`rbx` may be either state); and it is constant
time. -/
structure BothOk (H : Hash) (hH : HashOK H) : Prop where
  ok : ∀ {sc : Nat} {s₀ : State}, Pre H sc s₀ → ∀ {t : State}, KR H s₀ (inn s₀) t →
    t.gpr .rsi = bufOf H (inn s₀) → ∀ {Q : State → Prop},
    (∀ s' b, KR H s₀ b s' →
      hH.md.stateAt s'.mem (inn s₀) =
        hH.md.compress (hH.md.stateAt t.mem (inn s₀)) (hH.md.blockAt t.mem (bufOf H (inn s₀))) →
      hH.md.stateAt s'.mem (out s₀) =
        hH.md.compress (hH.md.stateAt t.mem (out s₀)) (hH.md.blockAt t.mem (bufOf H (out s₀))) →
      Q s') → WP isa H.compBoth t Q
  rel : ∀ {sc : Nat} {s₀ s₀' : State}, Pre H sc s₀ → Pre H sc s₀' → PubEq s₀ s₀' →
    RelCT isa (fun s s' => (KR H s₀ (inn s₀) s ∧ s.gpr .rsi = bufOf H (inn s₀)) ∧
        (KR H s₀' (inn s₀) s' ∧ s'.gpr .rsi = bufOf H (inn s₀)))
      H.compBoth fun s s' => ∃ b, KR H s₀ b s ∧ KR H s₀' b s'

section
variable {sc : Nat} {s₀ : State} (hp : Pre H sc s₀)
include hH hp

/-- A hash value away from what was written is the same. -/
theorem stateAt_keep {rs : List Region} {m m' : Mem} {p : Addr} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, H.P.N⟩ r) : hH.md.stateAt m' p = hH.md.stateAt m p := by
  obtain ⟨-, -, hN, -⟩ := sizes hH hp
  exact hH.md.stateAt_congr fun i hi =>
    hf.bytes (R := ⟨_, H.P.N⟩) hd (by show H.P.N ≤ 2 ^ 64; omega_using [hN]) hi

/-- A block away from what was written is the same. -/
theorem blockAt_keep {rs : List Region} {m m' : Mem} {p : Addr} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, H.P.B⟩ r) : hH.md.blockAt m' p = hH.md.blockAt m p := by
  obtain ⟨-, -, -, -, hB, -⟩ := sizes hH hp
  exact hH.md.parse_congr fun k hk =>
    hf.bytes (R := ⟨_, H.P.B⟩) hd (by show H.P.B ≤ 2 ^ 64; omega_using [hB]) hk

/-! ## Correctness -/

theorem blockKey_eq : blockKey hH.SH.H (bytesAt s₀.mem (kp s₀) (kl s₀)) = k0 H s₀ := by
  have := hp.kl_le
  simp only [blockKey, k0, K0, bytesAt_length, hH.hB, show ¬ (H.P.B < kl s₀) by omega_using [this], ↓reduceIte]

theorem correct (hbo : BothOk H hH) : WP isa H.hmacInit s₀ fun s' => gprPreserved s₀ s' ∧ (initG hH.SH sc).post s₀ s' := by
  obtain ⟨-, -, hN, hB0, hB, -, -, hW, hL, -⟩ := sizes hH hp
  have hkl := hp.kl_le
  obtain si := stOk_in (H := H) hp
  obtain so := stOk_out (H := H) hp
  obtain hsc : scR sc s₀ ∈ s₀.wr := by rw [hp.wr]; simp
  refine WP.seq (WP.mono (pro_ok hH hp) fun s₁ k₁ => ?_)
  refine WP.seq (callInit_ok hH hp k₁ (st := .rbx) k₁.rbx si fun s₂ k₂ f₂ r₂ => ?_)
  refine WP.seq (callInit_ok hH hp k₂ (st := .r12) k₂.r12 so fun s₃ k₃ f₃ r₃ => ?_)
  refine WP.seq (WP.mono (keys_ok hH hp k₃) fun s₄ ⟨k₄, si₄, f₄, bI₄, bO₄⟩ => ?_)
  refine WP.seq (hbo.ok hp k₄ si₄ fun s₇ b k₇ eI eO => ?_)
  refine WP.mono (restore_ok H.stream k₇.r15 hW k₇.saved (by rw [k₇.wr]; exact hsc) hL)
    fun s' ⟨hm, _, _, hg, ho⟩ => ⟨⟨fun r hr => ?_, by rw [hm, k₇.ret]⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hg _ (by simp)
    · exact hg _ (by simp)
    · rw [ho _ (by simp), k₇.rsp]
    · exact hg _ (by simp)
    · exact hg _ (by simp)
    · exact hg _ (by simp)
    · exact hg _ (by simp)
  -- What each piece keeps: the hash values and the buffers it does not write.
  obtain keepS : ∀ {rs : List Region} {m m' : Mem} {p : Addr}, Frame rs m m' →
      (∀ r ∈ rs, Region.Disjoint ⟨p, H.P.N⟩ r) → hH.md.stateAt m' p = hH.md.stateAt m p :=
    fun hf hd => hH.md.stateAt_congr fun i hi =>
      hf.bytes (R := ⟨_, H.P.N⟩) hd (by show H.P.N ≤ 2 ^ 64; omega_using [hN]) hi
  obtain hvI : Region.Sub ⟨inn s₀, H.P.N⟩ (inR H s₀) := Region.sub_prefix (by show H.P.N ≤ H.P.N + H.P.B; omega_using [])
  obtain hvO : Region.Sub ⟨out s₀, H.P.N⟩ (outR H s₀) := Region.sub_prefix (by show H.P.N ≤ H.P.N + H.P.B; omega_using [])
  obtain bI : Region.Sub ⟨bufOf H (inn s₀), H.P.B⟩ (inR H s₀) := Offset.sub_base _ (Nat.le_refl _)
  obtain bO : Region.Sub ⟨bufOf H (out s₀), H.P.B⟩ (outR H s₀) := Offset.sub_base _ (Nat.le_refl _)
  obtain nb : ∀ p : Addr, Region.Disjoint ⟨p, H.P.N⟩ ⟨bufOf H p, H.P.B⟩ := fun p =>
    Offset.base_disjoint _ (Nat.le_refl _) (by omega_using [hN, hB])
  obtain iv : ∀ {m : Mem} {p : Addr}, hH.SH.Repr m p [] → hH.md.stateAt m p = hH.iv := fun h => by
    have := ((hH.repr _ _ _).1 h).1
    rwa [List.length_nil, Nat.zero_div, Md.compressList_zero] at this
  -- The inner state.
  obtain iv₄ : hH.md.stateAt s₄.mem (inn s₀) = hH.iv := by
    rw [keepS f₄ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro r (rfl | rfl)
        · exact nb _
        · exact (hp.i_o.sub_left hvI).sub_right bO),
      keepS f₃ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro r (rfl | rfl)
        · exact hp.i_o.sub_left hvI
        · exact hp.stk_i.symm.sub_left hvI), iv r₂]
  obtain hl : (xorPad (k0 H s₀) ipad).length = H.P.B := by
    rw [Proof.Hmac.Common.xorPad_length, K0_length _ _ hkl]
  obtain rI := Md.repr_block (H := hH.md) (iv := hH.iv) hB0 hl bI₄ (eI.trans (congrArg (hH.md.compress · _) iv₄))
  -- The outer state.
  obtain ivO₄ : hH.md.stateAt s₄.mem (out s₀) = hH.iv := by
    rw [keepS f₄ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro r (rfl | rfl)
        · exact (hp.i_o.symm.sub_left hvO).sub_right bI
        · exact nb _), iv r₃]
  obtain hl' : (xorPad (k0 H s₀) opad).length = H.P.B := by
    rw [Proof.Hmac.Common.xorPad_length, K0_length _ _ hkl]
  obtain rO := Md.repr_block (H := hH.md) (iv := hH.iv) hB0 hl' bO₄ (eO.trans (congrArg (hH.md.compress · _) ivO₄))
  show hH.SH.Repr s'.mem (inn s₀) _ ∧ hH.SH.Repr s'.mem (out s₀) _
  rw [hm, blockKey_eq hH hp]
  exact ⟨(hH.repr _ _ _).2 rI, (hH.repr _ _ _).2 rO⟩

end

/-! ## Constant time -/

/-- The taint checks of the pieces of `init` between its calls. -/
structure Checks (H : Hash) : Prop where
  pro : ∃ hc, (Taint.check taint (Taint.ofRegs args) (.block H.initPrologue) hc).isSome = true
  argI : ∀ st ∈ [Reg.rbx, .r12], ∃ hc, (Taint.check taint (Taint.ofRegs kregs) (.block [.mov .rdi (.reg st)])
    hc).isSome = true
  keys : ∃ hc, (Taint.check taint (Taint.ofRegs kregs) H.initKeys hc).isSome = true
  mid : ∃ hc, (Taint.check taint (Taint.ofRegs kregs) (.block H.initOuter) hc).isSome = true
  restore : ∃ hc, (Taint.check taint (Taint.ofRegs kregs) (.block H.stream.restore) hc).isSome = true

section
variable {sc : Nat} {s₀ s₀' : State} (hp : Pre H sc s₀) (hp' : Pre H sc s₀') (hq : PubEq s₀ s₀')

omit hH in
theorem kr_agree (hq : PubEq s₀ s₀') {b : Addr} {s s' : State} (h : KR H s₀ b s) (h' : KR H s₀' b s') :
    ∀ r ∈ kregs, s.gpr r = s'.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h.rbx, h'.rbx]
  · rw [h.rbp, h'.rbp, kp, kp, hq.rdx]
  · rw [h.r12, h'.r12, out, out, hq.rsi]
  · rw [h.r13, h'.r13, hq.rcx]
  · rw [h.r15, h'.r15, scr, scr, hq.r8]
  · rw [h.rsp, h'.rsp, hq.rsp]

include hH hp hp' hq

/-- A call of the streaming `init` on the state at `p`, from `st`. -/
theorem callInit_rel (hc : Checks H) {b : Addr} {st : Reg} (hst : st ∈ [Reg.rbx, .r12]) {p : Addr}
    (hs : StOk (H := H) (sc := sc) (s₀ := s₀) p) (hs' : StOk (H := H) (sc := sc) (s₀ := s₀') p)
    (hr : ∀ {t : State}, KR H s₀ b t → t.gpr st = p) (hr' : ∀ {t : State}, KR H s₀' b t → t.gpr st = p) :
    RelCT isa (fun s s' => KR H s₀ b s ∧ KR H s₀' b s') (H.stream.callInit st)
      fun s s' => KR H s₀ b s ∧ KR H s₀' b s' := by
  obtain ha : RelCT isa (fun s s' => KR H s₀ b s ∧ KR H s₀' b s') (.block [.mov .rdi (.reg st)])
      fun s s' => (KR H s₀ b s ∧ s.gpr .rdi = p) ∧ (KR H s₀' b s' ∧ s'.gpr .rdi = p) :=
    rel_taint kregs (fun _ _ h h' => kr_agree hq h h') (hc.argI st hst)
      (fun _ h => wp_mov fun t u _ _ => WP.block_nil ⟨h.regs u.rd u.wr (fun r hr => u.other r (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) u.mem, by rw [u.gpr, hr h]⟩)
      (fun _ h => wp_mov fun t u _ _ => WP.block_nil ⟨h.regs u.rd u.wr (fun r hr => u.other r (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) u.mem, by rw [u.gpr, hr' h]⟩)
  obtain call : ∀ {t₀ : State}, Pre H sc t₀ → StOk (H := H) (sc := sc) (s₀ := t₀) p → ∀ t, KR H t₀ b t →
      t.gpr .rdi = p → WP isa (.call H.stream.initN H.stream.initC) t (KR H t₀ b) := fun hpt hst t k d => by
    refine init_call hH.stream (st := p) d (by rw [k.wr]; exact covers_one hst.mem)
      (by rw [k.rsp]; exact hst.stk) fun s' ha _ => ?_
    have f := ha.frame
    rw [k.rsp] at f
    refine k.keep ha.rd ha.wr (fun r hr => ha.cs r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [calleeSaved])) f ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact away_st hH hpt hst (fun _ h => h)
    · exact away_stk hH hpt (fun _ h => h)
  refine ha.seq (rel_wp (F := fun s => KR H s₀ b s ∧ s.gpr .rdi = p)
    (F' := fun s => KR H s₀' b s ∧ s.gpr .rdi = p) (init_rel hH.stream (st := p) fun s s' h => ?_)
    (fun t ⟨k, d⟩ => call hp hs t k d) (fun t ⟨k, d⟩ => call hp' hs' t k d))
  obtain ⟨⟨k, d⟩, ⟨k', d'⟩⟩ := h
  exact ⟨d, d', by rw [k.wr]; exact covers_one hs.mem, by rw [k'.wr]; exact covers_one hs'.mem,
    by rw [k.rsp]; exact hs.stk, by rw [k'.rsp]; exact hs'.stk, by rw [k.rsp, k'.rsp, hq.rsp]⟩

/-- A compression of the state at `p`. -/
theorem cmp_rel {p : Addr} (hs : StOk (H := H) (sc := sc) (s₀ := s₀) p)
    (hs' : StOk (H := H) (sc := sc) (s₀ := s₀') p) :
    RelCT isa (fun s s' => (KR H s₀ p s ∧ s.gpr .rsi = bufOf H p) ∧ (KR H s₀' p s' ∧ s'.gpr .rsi = bufOf H p))
      (compressAt H.compN H.compC) fun s s' => KR H s₀ p s ∧ KR H s₀' p s' :=
  rel_wp (compressAt_rel hH.md hH.comp fun s s' ⟨⟨k, si⟩, ⟨k', si'⟩⟩ =>
      ⟨⟨_, _, _, callOk hH hp hs k si⟩, ⟨_, _, _, callOk hH hp' hs' k' si'⟩,
        by rw [k.rbx, k'.rbx], by rw [k.r15, k'.r15, scr, scr, hq.r8], by rw [si, si'],
        by rw [k.rsp, k'.rsp, hq.rsp]⟩)
    (fun s ⟨k, si⟩ => cmp_ok hH hp hs k si fun s' k' _ _ => k')
    (fun s ⟨k, si⟩ => cmp_ok hH hp' hs' k si fun s' k' _ _ => k')

/-- From the inner state to the outer one. -/
theorem mid_rel (hc : Checks H) :
    RelCT isa (fun s s' => KR H s₀ (inn s₀) s ∧ KR H s₀' (inn s₀) s') (.block H.initOuter)
      fun s s' => (KR H s₀ (out s₀) s ∧ s.gpr .rsi = bufOf H (out s₀)) ∧
        (KR H s₀' (out s₀) s' ∧ s'.gpr .rsi = bufOf H (out s₀)) := by
  have ei : inn s₀' = inn s₀ := hq.rdi.symm
  have eo : out s₀' = out s₀ := hq.rsi.symm
  exact rel_taint kregs (fun _ _ h h' => kr_agree hq h h') hc.mid
    (fun _ h => WP.mono (mid_ok hH hp h) fun _ h => ⟨h.1, h.2.1⟩)
    (fun _ h => WP.mono (mid_ok hH hp' (ei ▸ h)) fun _ h => ⟨eo ▸ h.1, by rw [h.2.1, eo]⟩)

theorem ct (hbo : BothOk H hH) (hc : Checks H) :
    RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') H.hmacInit fun _ _ => True := by
  have ei : inn s₀' = inn s₀ := hq.rdi.symm
  have eo : out s₀' = out s₀ := hq.rsi.symm
  obtain si := stOk_in (H := H) hp
  obtain so := stOk_out (H := H) hp
  obtain si' : StOk (H := H) (sc := sc) (s₀ := s₀') (inn s₀) := ei ▸ stOk_in (H := H) hp'
  obtain so' : StOk (H := H) (sc := sc) (s₀ := s₀') (out s₀) := eo ▸ stOk_out (H := H) hp'
  obtain pro : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') (.block H.initPrologue)
      fun s s' => KR H s₀ (inn s₀) s ∧ KR H s₀' (inn s₀) s' :=
    rel_taint args (fun s s' e e' r hr => by
        rw [e, e']
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
        · exact hq.rdi
        · exact hq.rsi
        · exact hq.rdx
        · exact hq.rcx
        · exact hq.r8
        · exact hq.rsp) hc.pro
      (fun _ e => by rw [e]; exact pro_ok hH hp)
      (fun _ e => by rw [e, ← ei]; exact pro_ok hH hp')
  obtain c₁ := callInit_rel hH hp hp' hq hc (b := inn s₀) (st := .rbx) (by simp) si si'
    (fun k => k.rbx) (fun k => k.rbx)
  obtain c₂ := callInit_rel hH hp hp' hq hc (b := inn s₀) (st := .r12) (by simp) so so'
    (fun k => k.r12) (fun k => by rw [k.r12, eo])
  obtain keys : RelCT isa (fun s s' => KR H s₀ (inn s₀) s ∧ KR H s₀' (inn s₀) s') H.initKeys
      fun s s' => (KR H s₀ (inn s₀) s ∧ s.gpr .rsi = bufOf H (inn s₀)) ∧
        (KR H s₀' (inn s₀) s' ∧ s'.gpr .rsi = bufOf H (inn s₀)) :=
    rel_taint kregs (fun _ _ h h' => kr_agree hq h h') hc.keys
      (fun _ h => WP.mono (keys_ok hH hp h) fun _ h => ⟨h.1, h.2.1⟩)
      (fun _ h => WP.mono (keys_ok hH hp' (ei ▸ h)) fun _ h => ⟨ei ▸ h.1, by rw [h.2.1, ei]⟩)
  obtain ⟨_, hr⟩ := hc.restore
  obtain restore : RelCT isa (fun s s' => ∃ b, KR H s₀ b s ∧ KR H s₀' b s') (.block H.stream.restore)
      fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs kregs)
      (fun _ _ ⟨_, h, h'⟩ => Taint.agree_ofRegs (kr_agree hq h h')) hr
  exact pro.seq (c₁.seq (c₂.seq (keys.seq ((hbo.rel hp hp' hq).seq restore))))

end

/-- `compBoth` as the compression function on the inner state's block and
then on the outer's (`compTwice`). -/
theorem BothOk.twice (hc : Checks H)
    (h : H.compBoth = Impl.Pbkdf2.Md.X86_64.compTwice H.P.N H.compN H.compC) : BothOk H hH where
  ok {sc s₀} hp {t} hk hsi {Q} k := by
    obtain si := stOk_in (H := H) hp
    obtain so := stOk_out (H := H) hp
    obtain hvI : Region.Sub ⟨inn s₀, H.P.N⟩ (inR H s₀) :=
      Region.sub_prefix (by show H.P.N ≤ H.P.N + H.P.B; omega_using [])
    obtain hvO : Region.Sub ⟨out s₀, H.P.N⟩ (outR H s₀) :=
      Region.sub_prefix (by show H.P.N ≤ H.P.N + H.P.B; omega_using [])
    obtain bO : Region.Sub ⟨bufOf H (out s₀), H.P.B⟩ (outR H s₀) := Offset.sub_base _ (Nat.le_refl _)
    rw [h]
    refine WP.seq (cmp_ok hH hp si hk hsi fun s₅ k₅ f₅ e₅ => ?_)
    refine WP.seq (WP.mono (mid_ok hH hp k₅) fun s₆ ⟨k₆, si₆, m₆⟩ => ?_)
    refine cmp_ok hH hp so k₆ si₆ fun s₇ k₇ f₇ e₇ => k s₇ _ k₇ ?_ ?_
    · rw [stateAt_keep hH hp f₇ (by
          simp only [List.mem_cons, List.not_mem_nil, or_false]
          rintro r (rfl | rfl | rfl)
          · exact (hp.i_o.sub_right hvO).sub_left hvI
          · exact (hp.i_s.sub_right (cal_sub hH hp)).sub_left hvI
          · exact hp.stk_i.symm.sub_left hvI), m₆, e₅]
    · rw [e₇, m₆, stateAt_keep hH hp f₅ (by
          simp only [List.mem_cons, List.not_mem_nil, or_false]
          rintro r (rfl | rfl | rfl)
          · exact (hp.i_o.symm.sub_left hvO).sub_right hvI
          · exact (so.sc.sub_left hvO).sub_right (cal_sub hH hp)
          · exact so.stk.symm.sub_left hvO),
        blockAt_keep hH hp f₅ (by
          simp only [List.mem_cons, List.not_mem_nil, or_false]
          rintro r (rfl | rfl | rfl)
          · exact (hp.i_o.symm.sub_left bO).sub_right hvI
          · exact (so.sc.sub_left bO).sub_right (cal_sub hH hp)
          · exact so.stk.symm.sub_left bO)]
  rel {sc s₀ s₀'} hp hp' hq := by
    have ei : inn s₀' = inn s₀ := hq.rdi.symm
    have eo : out s₀' = out s₀ := hq.rsi.symm
    obtain si := stOk_in (H := H) hp
    obtain so := stOk_out (H := H) hp
    obtain si' : StOk (H := H) (sc := sc) (s₀ := s₀') (inn s₀) := ei ▸ stOk_in (H := H) hp'
    obtain so' : StOk (H := H) (sc := sc) (s₀ := s₀') (out s₀) := eo ▸ stOk_out (H := H) hp'
    rw [h]
    exact ((cmp_rel hH hp hp' hq si si').seq ((mid_rel hH hp hp' hq hc).seq
      (cmp_rel hH hp hp' hq so so'))).mono (fun _ _ h => h) fun _ _ h => ⟨_, h⟩

/-! ## Both compressions at once -/

/-- `s` is `t` with the arguments of such a function set up. -/
structure PairArgs (N : Nat) (t s : State) : Prop where
  rdi : s.gpr .rdi = t.gpr .rbx
  rdx : s.gpr .rdx = t.gpr .r12
  rcx : s.gpr .rcx = t.gpr .r12 + BitVec.ofNat 64 N
  r8 : s.gpr .r8 = t.gpr .r15
  other : ∀ r, r ≠ .rdi → r ≠ .rdx → r ≠ .rcx → r ≠ .r8 → s.gpr r = t.gpr r
  mem : s.mem = t.mem
  rd : s.rd = t.rd
  wr : s.wr = t.wr

omit hH in
theorem pairArgs_ok (N : Nat) (hN : N < 2 ^ 31) (s : State) :
    WP isa (.block (pairArgs N)) s (PairArgs N s) := by
  refine wp_mov fun s₁ u₁ _ _ => wp_mov fun s₂ u₂ _ _ => wp_mov fun s₃ u₃ _ _ => wp_addi fun s₄ u₄ =>
    wp_mov fun s₅ u₅ _ _ => WP.block_nil ⟨?_, ?_, ?_, ?_, fun r h1 h2 h3 h4 => ?_, ?_, ?_, ?_⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide)]
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), sx_ofNat hN]
  · rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  · rw [u₅.other r h4, u₄.other r h3, u₃.other r h3, u₂.other r h2, u₁.other r h1]
  · rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]

section
variable {sc : Nat} {s₀ : State} (hp : Pre H sc s₀)
include hH hp

/-- The precondition of a function that compresses both blocks at once, in
the state `s₁` with its arguments, set up from `t`. -/
theorem pair_pre {t s₁ : State} (hk : KR H s₀ (inn s₀) t) (hsi : t.gpr .rsi = bufOf H (inn s₀))
    (ha : PairArgs H.P.N t s₁) :
    (MdStream.X86_64.compress2K hH.md).pre (s₁.callEntry.withRegions
      [⟨bufOf H (inn s₀), H.P.B⟩, ⟨bufOf H (out s₀), H.P.B⟩] [⟨inn s₀, H.P.N⟩, ⟨out s₀, H.P.N⟩, calR H s₀]) ∧
    Covers ([⟨bufOf H (inn s₀), H.P.B⟩, ⟨bufOf H (out s₀), H.P.B⟩] ++ [⟨inn s₀, H.P.N⟩, ⟨out s₀, H.P.N⟩, calR H s₀])
      (s₁.rd ++ s₁.wr) ∧
    Covers [⟨inn s₀, H.P.N⟩, ⟨out s₀, H.P.N⟩, calR H s₀] s₁.wr := by
  obtain ⟨e1, e2, e3, e4, eo, -, erd, ewr⟩ := ha
  obtain ⟨_, s₆, _, k₆, si₆, m₆⟩ := mid_ok hH hp hk
  obtain c₀ := callOk hH hp (stOk_in (H := H) hp) hk hsi
  obtain c₁ := callOk hH hp (stOk_out (H := H) hp) k₆ si₆
  obtain hne : ∀ r : Reg, r ≠ .rsp → s₁.callEntry.gpr r = s₁.gpr r := fun r h => State.callEntry_gpr _ h
  simp only [MdStream.X86_64.compress2K, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    State.callEntry_rsp, hne _ (by decide : Reg.rdi ≠ .rsp), hne _ (by decide : Reg.rsi ≠ .rsp),
    hne _ (by decide : Reg.rdx ≠ .rsp), hne _ (by decide : Reg.rcx ≠ .rsp), hne _ (by decide : Reg.r8 ≠ .rsp),
    e1, e2, e3, e4, eo .rsi (by decide) (by decide) (by decide) (by decide),
    eo .rsp (by decide) (by decide) (by decide) (by decide), hk.rbx, hk.r12, hk.r15, hsi]
  obtain ⟨-, -, hN, -, hB, -⟩ := sizes hH hp
  obtain hvI : Region.Sub ⟨inn s₀, H.P.N⟩ (inR H s₀) :=
    Region.sub_prefix (by show H.P.N ≤ H.P.N + H.P.B; omega_using [])
  obtain hvO : Region.Sub ⟨out s₀, H.P.N⟩ (outR H s₀) :=
    Region.sub_prefix (by show H.P.N ≤ H.P.N + H.P.B; omega_using [])
  obtain bI : Region.Sub ⟨bufOf H (inn s₀), H.P.B⟩ (inR H s₀) := Offset.sub_base _ (Nat.le_refl _)
  obtain bO : Region.Sub ⟨bufOf H (out s₀), H.P.B⟩ (outR H s₀) := Offset.sub_base _ (Nat.le_refl _)
  obtain r₁ : s₆.gpr .rsp = t.gpr .rsp := k₆.rsp.trans hk.rsp.symm
  obtain cv : ∀ {X : List Region}, Covers [⟨bufOf H (inn s₀), H.P.B⟩, ⟨inn s₀, H.P.N⟩, calR H s₀] X →
      Covers [⟨bufOf H (out s₀), H.P.B⟩, ⟨out s₀, H.P.N⟩, calR H s₀] X →
      Covers ([⟨bufOf H (inn s₀), H.P.B⟩, ⟨bufOf H (out s₀), H.P.B⟩] ++
        [⟨inn s₀, H.P.N⟩, ⟨out s₀, H.P.N⟩, calR H s₀]) X := by
    intro X h₀ h₁ a n ⟨r, hr, hc⟩
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact h₀ a n ⟨_, by simp, hc⟩
    · exact h₁ a n ⟨_, by simp, hc⟩
    · exact h₀ a n ⟨_, by simp, hc⟩
    · exact h₁ a n ⟨_, by simp, hc⟩
    · exact h₀ a n ⟨_, by simp, hc⟩
  obtain cw : ∀ {X : List Region}, Covers [⟨inn s₀, H.P.N⟩, calR H s₀] X → Covers [⟨out s₀, H.P.N⟩, calR H s₀] X →
      Covers [⟨inn s₀, H.P.N⟩, ⟨out s₀, H.P.N⟩, calR H s₀] X := by
    intro X h₀ h₁ a n ⟨r, hr, hc⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h₀ a n ⟨_, by simp, hc⟩
    · exact h₁ a n ⟨_, by simp, hc⟩
    · exact h₀ a n ⟨_, by simp, hc⟩
  refine ⟨⟨trivial, trivial, (hp.i_o.sub_left hvI).sub_right hvO, c₀.d₁, c₁.d₁, c₀.d₂,
    (hp.i_o.sub_left bI).sub_right hvO, c₀.d₃, (hp.i_o.symm.sub_left bO).sub_right hvI, c₁.d₂, c₁.d₃, c₀.d₄,
    r₁ ▸ c₁.d₄, c₀.d₅⟩, ?_, ?_⟩
  · rw [erd, ewr]
    exact cv c₀.hc (by rw [hk.rd, hk.wr, ← k₆.rd, ← k₆.wr]; exact c₁.hc)
  · rw [ewr]
    exact cw c₀.hw (by rw [hk.wr, ← k₆.wr]; exact c₁.hw)

/-- The call of a function that compresses both blocks at once. -/
theorem pair_ok {name : String} {code : Prog isa} (hf : MdStream.X86_64.PairOk hH.md code) {t : State}
    (hk : KR H s₀ (inn s₀) t) (hsi : t.gpr .rsi = bufOf H (inn s₀)) {Q : State → Prop}
    (k : ∀ s', KR H s₀ (inn s₀) s' →
      hH.md.stateAt s'.mem (inn s₀) =
        hH.md.compress (hH.md.stateAt t.mem (inn s₀)) (hH.md.blockAt t.mem (bufOf H (inn s₀))) →
      hH.md.stateAt s'.mem (out s₀) =
        hH.md.compress (hH.md.stateAt t.mem (out s₀)) (hH.md.blockAt t.mem (bufOf H (out s₀))) →
      Q s') :
    WP isa (Impl.Pbkdf2.Md.X86_64.compPair H.P.N name code) t Q := by
  obtain ⟨-, -, hN, -, hB, -⟩ := sizes hH hp
  obtain si := stOk_in (H := H) hp
  obtain so := stOk_out (H := H) hp
  obtain hvI : Region.Sub ⟨inn s₀, H.P.N⟩ (inR H s₀) :=
    Region.sub_prefix (by show H.P.N ≤ H.P.N + H.P.B; omega_using [])
  obtain hvO : Region.Sub ⟨out s₀, H.P.N⟩ (outR H s₀) :=
    Region.sub_prefix (by show H.P.N ≤ H.P.N + H.P.B; omega_using [])
  obtain bI : Region.Sub ⟨bufOf H (inn s₀), H.P.B⟩ (inR H s₀) := Offset.sub_base _ (Nat.le_refl _)
  obtain bO : Region.Sub ⟨bufOf H (out s₀), H.P.B⟩ (outR H s₀) := Offset.sub_base _ (Nat.le_refl _)
  obtain b8 : Region.Sub (below (t.gpr .rsp) 8) (stkR s₀) := by
    rw [hk.rsp]; exact Offset.sub_below _ (by omega_using []) (by omega_using [])
  show WP isa (.seq (.block (pairArgs H.P.N)) (.call name code)) t Q
  refine WP.seq (WP.mono (pairArgs_ok H.P.N (by omega_using [hN]) t) fun s₁ ha => ?_)
  obtain ⟨hpre, hc, hw⟩ := pair_pre hH hp hk hsi ha
  obtain hsp : s₁.gpr .rsp = t.gpr .rsp := ha.other _ (by decide) (by decide) (by decide) (by decide)
  refine WP.call (k := MdStream.X86_64.compress2K hH.md) hf.verified hf.nosp (by rw [hf.depth]; decide)
    hpre hc hw ?_
  intro s₂ hrd hwr hcs hfr _ ⟨s₃, hm₃, _, hpost⟩
  obtain hne : ∀ r : Reg, r ≠ .rsp → s₁.callEntry.gpr r = s₁.gpr r := fun r h => State.callEntry_gpr _ h
  simp only [MdStream.X86_64.compress2K, State.withRegions_gpr, State.withRegions_mem,
    hne _ (by decide : Reg.rdi ≠ .rsp), hne _ (by decide : Reg.rsi ≠ .rsp), hne _ (by decide : Reg.rdx ≠ .rsp),
    hne _ (by decide : Reg.rcx ≠ .rsp), ha.rdi, ha.rdx, ha.rcx,
    ha.other .rsi (by decide) (by decide) (by decide) (by decide), hk.rbx, hk.r12, hsi, hm₃] at hpost
  obtain f : Frame [⟨inn s₀, H.P.N⟩, ⟨out s₀, H.P.N⟩, calR H s₀, stkR s₀] t.mem s₂.mem := by
    rw [hf.depth, hsp, ha.mem] at hfr
    exact hfr.sub fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨⟨out s₀, H.P.N⟩, by simp, fun _ h => h⟩
      · exact ⟨calR H s₀, by simp, fun _ h => h⟩
      · exact ⟨stkR s₀, by simp, b8⟩
  obtain fe : Frame [below (t.gpr .rsp) 8] t.mem s₁.callEntry.mem := by
    rw [← hsp, ← ha.mem]
    exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (below_call _ (by omega_using []) (by omega_using []))
  obtain one : ∀ {X : Region}, (below (t.gpr .rsp) 8).Disjoint X → ∀ r ∈ [below (t.gpr .rsp) 8], X.Disjoint r :=
    fun h r hr => by rw [List.mem_singleton.mp hr]; exact h.symm
  rw [stateAt_keep hH hp fe (one ((si.stk.sub_left b8).sub_right hvI)),
    blockAt_keep hH hp fe (one ((si.stk.sub_left b8).sub_right bI)),
    stateAt_keep hH hp fe (one ((so.stk.sub_left b8).sub_right hvO)),
    blockAt_keep hH hp fe (one ((so.stk.sub_left b8).sub_right bO))] at hpost
  refine k s₂ (hk.keep (hrd.trans ha.rd) (hwr.trans ha.wr) (fun r hr => ?_) f ?_) hpost.1 hpost.2
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact (hcs _ (by simp [calleeSaved])).trans (ha.other _ (by decide) (by decide) (by decide) (by decide))
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact away_st hH hp si hvI
    · exact away_st hH hp so hvO
    · exact away_cal hH hp
    · exact away_stk hH hp (fun _ h => h)

end

/-- `compBoth` as one call of a function that compresses both blocks at once
(`compPair`). -/
theorem BothOk.pair {name : String} {code : Prog isa} (hf : MdStream.X86_64.PairOk hH.md code)
    (hta : ∃ hc, (Taint.check taint (Taint.ofRegs kregs) (.block (pairArgs H.P.N)) hc).isSome = true)
    (h : H.compBoth = Impl.Pbkdf2.Md.X86_64.compPair H.P.N name code) : BothOk H hH where
  ok {sc s₀} hp {t} hk hsi {Q} k := by
    rw [h]; exact pair_ok hH hp hf hk hsi fun s' k' e₁ e₂ => k s' _ k' e₁ e₂
  rel {sc s₀ s₀'} hp hp' hq := by
    have ei : inn s₀' = inn s₀ := hq.rdi.symm
    have eo : out s₀' = out s₀ := hq.rsi.symm
    obtain ⟨-, -, hN, -⟩ := sizes hH hp
    rw [h]
    obtain args : RelCT isa (fun s s' => (KR H s₀ (inn s₀) s ∧ s.gpr .rsi = bufOf H (inn s₀)) ∧
          (KR H s₀' (inn s₀) s' ∧ s'.gpr .rsi = bufOf H (inn s₀))) (.block (pairArgs H.P.N))
        fun s s' => (∃ t, (KR H s₀ (inn s₀) t ∧ t.gpr .rsi = bufOf H (inn s₀)) ∧ PairArgs H.P.N t s) ∧
          (∃ t, (KR H s₀' (inn s₀) t ∧ t.gpr .rsi = bufOf H (inn s₀)) ∧ PairArgs H.P.N t s') :=
      rel_taint kregs (fun _ _ h h' => kr_agree hq h.1 h'.1) hta
        (fun s h => WP.mono (pairArgs_ok H.P.N (by omega_using [hN]) s) fun _ a => ⟨s, h, a⟩)
        (fun s h => WP.mono (pairArgs_ok H.P.N (by omega_using [hN]) s) fun _ a => ⟨s, h, a⟩)
    obtain call := VG.X86_64.RelCT.callEx (n := name) (k := MdStream.X86_64.compress2K hH.md)
      (P := fun s s' => (∃ t, (KR H s₀ (inn s₀) t ∧ t.gpr .rsi = bufOf H (inn s₀)) ∧ PairArgs H.P.N t s) ∧
        (∃ t, (KR H s₀' (inn s₀) t ∧ t.gpr .rsi = bufOf H (inn s₀)) ∧ PairArgs H.P.N t s'))
      hf.verified hf.ct fun s₁ s₂ ⟨⟨t, ⟨k, si⟩, a⟩, ⟨t', ⟨k', si'⟩, a'⟩⟩ => by
        obtain ⟨p₁, c₁, w₁⟩ := pair_pre hH hp k si a
        obtain ⟨p₂, c₂, w₂⟩ := pair_pre hH hp' (ei ▸ k') (by rw [si', ei]) a'
        refine ⟨_, _, _, _, p₁, p₂, ?_, c₁, w₁, c₂, w₂, ?_⟩
        · simp only [MdStream.X86_64.compress2K, State.withRegions_gpr,
            State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
            State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp),
            State.callEntry_gpr _ (by decide : Reg.r8 ≠ .rsp)]
          exact ⟨by rw [a.rdi, a'.rdi, k.rbx, k'.rbx],
            by rw [a.other .rsi (by decide) (by decide) (by decide) (by decide),
              a'.other .rsi (by decide) (by decide) (by decide) (by decide), si, si'],
            by rw [a.rdx, a'.rdx, k.r12, k'.r12, eo], by rw [a.rcx, a'.rcx, k.r12, k'.r12, eo],
            by rw [a.r8, a'.r8, k.r15, k'.r15, scr, scr, hq.r8]⟩
        · rw [a.other .rsp (by decide) (by decide) (by decide) (by decide),
            a'.other .rsp (by decide) (by decide) (by decide) (by decide), k.rsp, k'.rsp, hq.rsp]
    exact (rel_wp (c := Impl.Pbkdf2.Md.X86_64.compPair H.P.N name code) (args.seq call)
      (fun s ⟨k, si⟩ => pair_ok hH hp hf k si fun s' k' _ _ => k')
      (fun s ⟨k, si⟩ => pair_ok hH hp' hf (ei ▸ k) (by rw [si, ei]) fun s' k' _ _ => ei ▸ k')).mono
        (fun _ _ h => h) fun _ _ h => ⟨_, h⟩

/-- What `init` needs of `H.compBoth`, whichever of the two it is. -/
theorem bothOk (hc : Checks H) : BothOk H hH := by
  rcases hH.both with h | ⟨name, code, h, hf, hta⟩
  · exact .twice hH hc h
  · exact .pair hH hf hta h

/-- HMAC's `init` is verified against `initG`, given the taint checks and the
facts about its code that the kernel checks for each hash function. -/
theorem verified {sc : Nat} (hbo : BothOk H hH) (hc : Checks H) (hfit : H.stream.buf ≤ 8 * sc)
    (hmx : H.hmacInit.allInstrs (fun i => !loadsMxcsr i) = true) (hsat : ∃ s, (initG hH.SH sc).pre s) :
    Verified X86_64.target H.hmacInit (initG hH.SH sc) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, hsat⟩
  · obtain ⟨t, s', he, hg, hpost⟩ := correct hH (pre_of hH hs hfit) hbo
    exact ⟨t, s', he, abiPreserved_of_exec hmx he hg, hpost⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hpub
    exact (ct hH (pre_of hH h₁ hfit) (pre_of hH h₂ hfit) ⟨h1, h2, h3, h4, h5, h6⟩ hbo hc
      _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.Pbkdf2.Md.X86_64.HmacInit

end

end

/-! ### `Pbkdf2.Md.X86_64.HmacFin`, which only this module used -/

section

/-! ### `Pbkdf2.Md.X86_64.HmacFinInner`, which only this module used -/

section

/-!
# HMAC over any Merkle–Damgård hash function on x86-64: `finalize` up to the inner digest

HMAC's `finalize` (`Impl/Pbkdf2/Md/X86_64.lean`) starts by saving our
caller's registers (`pro_ok`) and finalizing the inner state into `scratch`
with the streaming `finalize` (`fin1Args_ok`, `finCall_ok`): what holds from
the prologue on (`KR`), and that call in two runs (`fin_rel'`). The rest is
`Proof/Pbkdf2/Md/X86_64/HmacFin.lean`.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Md.X86_64.HmacFin

open VG.X86_64
open VG.Impl.Pbkdf2.Md.X86_64 (Stream)
open VG.Proof.Pbkdf2.Md.X86_64.Calls
open VG.Proof.Hmac.Generic.Common (off_disj off_disj0 covers_one sub_of_off sub_of_self)
open VG.Proof.Sha256.X86_64 (toNat_ofNat_lt sub_offset contains_offset)
open VG.Proof.Sha256.X86_64.Stream (Upd wp_mov wp_mov32i wp_addi)
open Spec.Sha256 (bytesAt)

variable {H : Stream} (hH : StreamOK H) (sc : Nat)

section
variable (s₀ : State)

abbrev inn : Addr := s₀.gpr .rdi
abbrev outer : Addr := s₀.gpr .rsi
abbrev op : Addr := s₀.gpr .rcx
abbrev scr : Addr := s₀.gpr .r8
abbrev inR : Region := ⟨inn s₀, H.S⟩
abbrev outerR : Region := ⟨outer s₀, H.S⟩
abbrev opR : Region := ⟨op s₀, H.D⟩
abbrev scR : Region := ⟨scr s₀, 8 * sc⟩
abbrev retR : Region := ⟨s₀.gpr .rsp, 8⟩
abbrev stkR : Region := below (s₀.gpr .rsp) 16
/-- Where the digests go. -/
abbrev T : Addr := scr s₀ + BitVec.ofNat 64 H.buf
abbrev tR : Region := ⟨T (H := H) s₀, H.F⟩
abbrev calR : Region := ⟨scr s₀, hH.Wb⟩

end

/-- The precondition, with the sizes of `H`. -/
structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [outerR (H := H) s₀]
  wr : s₀.wr = [inR (H := H) s₀, opR (H := H) s₀, scR sc s₀]
  i_o : (inR (H := H) s₀).Disjoint (outerR (H := H) s₀)
  i_p : (inR (H := H) s₀).Disjoint (opR (H := H) s₀)
  i_s : (inR (H := H) s₀).Disjoint (scR sc s₀)
  o_p : (outerR (H := H) s₀).Disjoint (opR (H := H) s₀)
  o_s : (outerR (H := H) s₀).Disjoint (scR sc s₀)
  p_s : (opR (H := H) s₀).Disjoint (scR sc s₀)
  ret_i : (retR s₀).Disjoint (inR (H := H) s₀)
  ret_o : (retR s₀).Disjoint (outerR (H := H) s₀)
  ret_p : (retR s₀).Disjoint (opR (H := H) s₀)
  ret_s : (retR s₀).Disjoint (scR sc s₀)
  stk_i : (stkR s₀).Disjoint (inR (H := H) s₀)
  stk_o : (stkR s₀).Disjoint (outerR (H := H) s₀)
  stk_p : (stkR s₀).Disjoint (opR (H := H) s₀)
  stk_s : (stkR s₀).Disjoint (scR sc s₀)
  nw : (scr s₀).toNat + 8 * sc ≤ 2 ^ 64
  fits : H.buf + H.F ≤ 8 * sc
  hB : 0 < H.B ∧ H.B ≤ 128
  hW : H.W ≤ 256
  hS : 0 < H.S ∧ H.S ≤ 256
  hD : 0 < H.D ∧ H.D ≤ H.F ∧ H.F ≤ 64

theorem pre_of {s₀ : State} (h : (finG hH.SH sc).pre s₀) (hfit : H.buf + H.F ≤ 8 * sc) :
    Pre (H := H) sc s₀ := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := h
  have hS := hH.hS
  have hD := hH.hD
  simp only [hS, hD] at *
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, hfit,
    ⟨hH.hB0, hH.hBB⟩, hH.hW, ⟨hH.hS0, hH.hSB⟩, ⟨hH.hD0, hH.hDF, hH.hF⟩⟩

/-! ## The parts of `scratch` -/

section
variable {sc : Nat} {s₀ : State} (hp : Pre (H := H) sc s₀)
include hp

theorem save_sub : Region.Sub (saveR H (scr s₀)) (scR sc s₀) := by
  have := hp.fits; have := hp.nw; have := hp.hW; simp only [Stream.buf] at *
  exact sub_offset (by omega_nat) (by omega_nat)

theorem t_sub : Region.Sub (tR (H := H) s₀) (scR sc s₀) := by
  have := hp.fits; have := hp.nw; have := hp.hD
  exact sub_offset hp.fits (by omega_nat)

include hH in
theorem cal_sub : Region.Sub (calR hH s₀) (scR sc s₀) := by
  have := hH.hWb; have := hp.fits; simp only [Stream.buf] at this
  exact Region.sub_prefix (by omega_nat)

include hH in
theorem cal_save : (calR hH s₀).Disjoint (saveR H (scr s₀)) := by
  have := hH.hWb; have := hp.fits; have := hp.nw; have := hp.hW; simp only [Stream.buf] at *
  exact off_disj0 (scr s₀) (m := hH.Wb) (b := 8 * H.W) (n := 48) (by omega_nat) (by omega_nat)

include hH in
theorem cal_t : (calR hH s₀).Disjoint (tR (H := H) s₀) := by
  have := hH.hWb; have := hp.fits; have := hp.nw; have := hp.hW; have := hp.hD; simp only [Stream.buf] at *
  exact off_disj0 (scr s₀) (m := hH.Wb) (b := 8 * H.W + 48) (n := H.F) (by omega_nat) (by omega_nat)

theorem save_t : (saveR H (scr s₀)).Disjoint (tR (H := H) s₀) := by
  have := hp.fits; have := hp.nw; have := hp.hW; have := hp.hD; simp only [Stream.buf] at *
  exact off_disj (scr s₀) (a := 8 * H.W) (m := 48) (b := 8 * H.W + 48) (n := H.F) (by omega_nat) (by omega_nat)
    (by omega_nat)

omit hp in
theorem stk_ret : (stkR s₀).Disjoint (retR s₀) :=
  Offset.below_disjoint _ (m := 16) (by omega_nat)

end

/-! ## What the calls keep -/

/-- The registers and memory kept from the prologue on. -/
structure KR (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rbx : s.gpr .rbx = inn s₀
  r12 : s.gpr .r12 = outer s₀
  r13 : s.gpr .r13 = op s₀
  r15 : s.gpr .r15 = scr s₀
  saved : SavedRegs H (scr s₀) s₀ s.mem
  ret : s.mem.readW (s₀.gpr .rsp) 64 = s₀.mem.readW (s₀.gpr .rsp) 64

/-- The registers `KR` fixes. -/
abbrev kregs : List Reg := [.rbx, .r12, .r13, .r15, .rsp]

theorem KR.keep {s₀ s s' : State} (h : KR (H := H) s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r ∈ kregs, s'.gpr r = s.gpr r) {rs : List Region}
    (hf : Frame rs s.mem s'.mem) (hs : ∀ r ∈ rs, (saveR H (scr s₀)).Disjoint r)
    (hr : ∀ r ∈ rs, (retR s₀).Disjoint r) : KR (H := H) s₀ s' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, (hg _ (by simp)).trans h.rsp, (hg _ (by simp)).trans h.rbx,
    (hg _ (by simp)).trans h.r12, (hg _ (by simp)).trans h.r13, (hg _ (by simp)).trans h.r15,
    h.saved.frame H hf hs, (hf.readW (r := retR s₀) (Region.contains_self _ _) hr (by decide)).trans h.ret⟩

theorem KR.regs {s₀ s s' : State} (h : KR (H := H) s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r ∈ kregs, s'.gpr r = s.gpr r) (hm : s'.mem = s.mem) : KR (H := H) s₀ s' :=
  h.keep hrd hwr hg (rs := []) (by rw [hm]; exact Frame.refl _ _) (by simp) (by simp)

theorem KR.call {s₀ s s' : State} (h : KR (H := H) s₀ s) {ws : List Region} (ha : After s ws s')
    (hs : ∀ r ∈ ws ++ [stkR s₀], (saveR H (scr s₀)).Disjoint r)
    (hr : ∀ r ∈ ws ++ [stkR s₀], (retR s₀).Disjoint r) : KR (H := H) s₀ s' := by
  have f := ha.frame
  rw [h.rsp] at f
  exact h.keep ha.rd ha.wr (fun r hr => ha.cs r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [calleeSaved])) f hs hr

/-! ## The pieces -/

section
variable {sc : Nat} {s₀ : State} (hp : Pre (H := H) sc s₀)
include hp

theorem wr_mem : scR sc s₀ ∈ s₀.wr ∧ inR (H := H) s₀ ∈ s₀.wr ∧ opR (H := H) s₀ ∈ s₀.wr := by
  rw [hp.wr]; simp

theorem pro_ok : WP isa (.block H.finPrologue) s₀ fun s => KR (H := H) s₀ s ∧ s.gpr .rdi = inn s₀ ∧
    s.gpr .rdx = s₀.gpr .rdx ∧ Frame [saveR H (scr s₀)] s₀.mem s.mem := by
  obtain hL : 8 * H.W + 48 ≤ 8 * sc := by have := hp.fits; simp only [Stream.buf] at this; omega_nat
  refine save_ok H (scr := scr s₀) rfl hp.hW (wr_mem hp).1 hL fun s₁ g₁ rd₁ wr₁ f₁ sv₁ => ?_
  refine wp_mov fun s₂ u₂ _ _ => wp_mov fun s₃ u₃ _ _ => wp_mov fun s₄ u₄ _ _ => wp_mov fun s₅ u₅ _ _ =>
    WP.block_nil ?_
  obtain k : ∀ r, r ≠ .rbx → r ≠ .r12 → r ≠ .r13 → r ≠ .r15 → s₅.gpr r = s₀.gpr r := fun r h1 h2 h3 h4 => by
    rw [u₅.other r h4, u₄.other r h3, u₃.other r h2, u₂.other r h1, g₁]
  obtain hm : s₅.mem = s₁.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem]
  refine ⟨⟨by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁], by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁],
    k _ (by decide) (by decide) (by decide) (by decide),
    by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, g₁],
    by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), g₁],
    by rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), g₁],
    by rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), g₁],
    hm ▸ sv₁, ?_⟩, k _ (by decide) (by decide) (by decide) (by decide),
    k _ (by decide) (by decide) (by decide) (by decide), hm ▸ f₁⟩
  rw [hm]
  exact (f₁.readW (r := retR s₀) (Region.contains_self _ _) (by
    simp only [List.mem_singleton]; rintro r rfl; exact hp.ret_s.sub_right (save_sub hp)) (by decide))

/-- The regions of a call of `finalize` on `inner`, into `T`. -/
theorem finArgs {t : State} (hk : KR (H := H) s₀ t) (hdi : t.gpr .rdi = inn s₀)
    (hdx : t.gpr .rdx = T (H := H) s₀) (hcx : t.gpr .rcx = scr s₀) :
    FinArgs hH t (inn s₀) (T (H := H) s₀) (scr s₀) := by
  obtain hwb := hH.hWb; have hf := hp.fits; simp only [Stream.buf] at hf
  obtain ⟨sR, iR, _⟩ := wr_mem hp
  exact
    { rdi := hdi, rdx := hdx, rcx := hcx
      cw := by
        rw [hk.wr]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact sub_of_self iR (Nat.le_refl _)
          · exact sub_of_off sR hp.fits
          · exact sub_of_self (r := scR sc s₀) sR (by show hH.Wb ≤ 8 * sc; omega_nat)
      st_o := hp.i_s.sub_right (t_sub hp)
      st_sc := hp.i_s.sub_right (cal_sub hH hp)
      o_sc := (cal_t hH hp).symm
      stk_st := by rw [hk.rsp]; exact hp.stk_i
      stk_o := by rw [hk.rsp]; exact hp.stk_s.sub_right (t_sub hp)
      stk_sc := by rw [hk.rsp]; exact hp.stk_s.sub_right (cal_sub hH hp) }

/-- The first call's arguments: the count from `rdx`. -/
theorem fin1Args_ok {s : State} (hk : KR (H := H) s₀ s) (hdi : s.gpr .rdi = inn s₀) {c : BitVec 64}
    (hdx : s.gpr .rdx = c) :
    WP isa (.block ([] ++ ([.mov .rsi (.reg .rdx)] : List Instr) ++ VG.Impl.Pbkdf2.Md.X86_64.scr .rdx H.buf ++
      ([.mov .rcx (.reg .r15)] : List Instr))) s fun t => KR (H := H) s₀ t ∧
        FinArgs hH t (inn s₀) (T (H := H) s₀) (scr s₀) ∧ t.gpr .rsi = c ∧ t.mem = s.mem := by
  obtain hf := hp.fits; have hW := hp.hW; have hbuf : H.buf = 8 * H.W + 48 := rfl
  simp only [VG.Impl.Pbkdf2.Md.X86_64.scr, List.cons_append, List.nil_append]
  refine wp_mov fun s₁ u₁ _ _ => wp_mov fun s₂ u₂ _ _ => wp_addi fun s₃ u₃ => wp_mov fun s₄ u₄ _ _ =>
    WP.block_nil ?_
  obtain k₄ : KR (H := H) s₀ s₄ := hk.regs (by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd])
    (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;>
        rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)])
    (by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem])
  refine ⟨k₄, finArgs hH hp k₄ ?_ ?_ ?_, ?_, by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]⟩
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hdi]
  · rw [u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.other _ (by decide), hk.r15, sx_ofNat (by omega_nat)]
  · rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hk.r15]
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hdx]

/-- The second call's arguments: the state at `rbx`, of `B + D` bytes. -/

theorem finCall_ok {t : State} (hk : KR (H := H) s₀ t) (ha : FinArgs hH t (inn s₀) (T (H := H) s₀) (scr s₀))
    {Q : State → Prop}
    (hQ : ∀ s', KR (H := H) s₀ s' → Frame [inR (H := H) s₀, tR (H := H) s₀, calR hH s₀, stkR s₀] t.mem s'.mem →
      (∀ m, hH.SH.Repr t.mem (inn s₀) m → m.length < 2 ^ 64 → t.gpr .rsi = BitVec.ofNat 64 m.length →
        (bytesAt s'.mem (T (H := H) s₀) H.F).take H.D = hH.SH.H.hash m) → Q s') :
    WP isa (.call H.finN H.finC) t Q :=
  fin_call hH ha fun s' ha' hpost => by
    have f := ha'.frame
    rw [hk.rsp] at f
    refine hQ s' (hk.call ha' ?_ ?_) f hpost
    · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl | rfl)
      · exact hp.i_s.symm.sub_left (save_sub hp)
      · exact save_t hp
      · exact (cal_save hH hp).symm
      · exact hp.stk_s.symm.sub_left (save_sub hp)
    · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl | rfl)
      · exact hp.ret_i
      · exact hp.ret_s.sub_right (t_sub hp)
      · exact hp.ret_s.sub_right (cal_sub hH hp)
      · exact (stk_ret (s₀ := s₀)).symm


end

/-! ## In two runs -/

/-- The block that sets up the first call of `finalize`. -/
abbrev fin1Block (H : Stream) : List Instr :=
  [] ++ ([.mov .rsi (.reg .rdx)] : List Instr) ++ VG.Impl.Pbkdf2.Md.X86_64.scr .rdx H.buf ++
    ([.mov .rcx (.reg .r15)] : List Instr)

variable {sc : Nat}
variable {s₀ s₀' : State} (hp : Pre (H := H) sc s₀) (hp' : Pre (H := H) sc s₀') (hq : PubEq s₀ s₀')

theorem kr_agree {s s' : State} (hq : PubEq s₀ s₀') (h : KR (H := H) s₀ s) (h' : KR (H := H) s₀' s') :
    ∀ r ∈ kregs, s.gpr r = s'.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [h.rbx, h'.rbx, inn, inn, hq.rdi]
  · rw [h.r12, h'.r12, outer, outer, hq.rsi]
  · rw [h.r13, h'.r13, op, op, hq.rcx]
  · rw [h.r15, h'.r15, scr, scr, hq.r8]
  · rw [h.rsp, h'.rsp, hq.rsp]

include hH hp hp' hq

omit hH hp hp' in
theorem eqs : inn s₀' = inn s₀ ∧ T (H := H) s₀' = T (H := H) s₀ ∧ scr s₀' = scr s₀ :=
  ⟨hq.rdi.symm, by show s₀'.gpr .r8 + _ = s₀.gpr .r8 + _; rw [hq.r8], hq.r8.symm⟩

/-- A call of `finalize` from a block that sets up its arguments. -/
theorem fin_rel' {blk : List Instr} {c : BitVec 64} {F F' : State → Prop}
    (hck : ∃ hc, (Taint.check taint (Taint.ofRegs kregs) (.block blk) hc).isSome = true)
    (hag : ∀ s s', F s → F' s' → ∀ r ∈ kregs, s.gpr r = s'.gpr r)
    (hb : ∀ s, F s → WP isa (.block blk) s fun t => KR (H := H) s₀ t ∧
      FinArgs hH t (inn s₀) (T (H := H) s₀) (scr s₀) ∧ t.gpr .rsi = c ∧ t.mem = s.mem)
    (hb' : ∀ s, F' s → WP isa (.block blk) s fun t => KR (H := H) s₀' t ∧
      FinArgs hH t (inn s₀') (T (H := H) s₀') (scr s₀') ∧ t.gpr .rsi = c ∧ t.mem = s.mem) :
    RelCT isa (fun s s' => F s ∧ F' s') (.seq (.block blk) (.call H.finN H.finC))
      fun s s' => KR (H := H) s₀ s ∧ KR (H := H) s₀' s' := by
  obtain ⟨e1, e2, e3⟩ := eqs hq
  obtain ha := rel_taint (G := fun t => KR (H := H) s₀ t ∧ FinArgs hH t (inn s₀) (T (H := H) s₀) (scr s₀) ∧
      t.gpr .rsi = c)
    (G' := fun t => KR (H := H) s₀' t ∧ FinArgs hH t (inn s₀) (T (H := H) s₀) (scr s₀) ∧ t.gpr .rsi = c)
    kregs hag hck (fun s h => WP.mono (hb s h) fun _ ⟨k, a, si, _⟩ => ⟨k, a, si⟩)
    (fun s h => WP.mono (hb' s h) fun _ ⟨k, a, si, _⟩ => ⟨k, e1 ▸ e2 ▸ e3 ▸ a, si⟩)
  refine ha.seq (rel_wp (fin_rel hH (st := inn s₀) (o := T (H := H) s₀) (sc := scr s₀)
    fun s s' ⟨⟨k, a, si⟩, ⟨k', a', si'⟩⟩ => ⟨a, a', by rw [si, si'], by rw [k.rsp, k'.rsp, hq.rsp]⟩)
    (fun _ ⟨k, a, _⟩ => finCall_ok hH hp k a fun _ k' _ _ => k')
    (fun _ ⟨k, a, _⟩ => finCall_ok hH hp' k (e1.symm ▸ e2.symm ▸ e3.symm ▸ a) fun _ k' _ _ => k'))

end VG.Proof.Pbkdf2.Md.X86_64.HmacFin

end

end


/-!
# HMAC over any Merkle–Damgård hash function on x86-64: `finalize`

HMAC's `finalize` (`Impl/Pbkdf2/Md/X86_64.lean`) starts by finalizing the
inner state into `scratch` (`Proof/Pbkdf2/Md/X86_64/HmacFinInner.lean`);
then it computes the outer hash with one compression, as `iterate`
does (`Proof/Pbkdf2/X86_64/Iterate.lean`): it writes the outer hash value over
the inner state's and, into its buffer, the inner digest and the padding
(`finMid`, `mid_ok`), compresses that block (`cmp_ok`) and writes the digest
of the result to `out` (`finOut`, `out_ok`). That this is the outer hash is
`Md.Link.hash_block`. Everything up to the inner digest is
`HmacFinInner.lean`'s, for the hash function's streaming functions
(`HashOK.stream`); constant time likewise, from the taint checks of the pieces between the calls
(`Checks`) and the compression function's own proof (`compressAt_rel`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Md.X86_64.HmacFin

open VG.X86_64 VG.Proof.MdStream
open VG.Proof.MdStream.X86_64 (add_ofNat sx_ofNat wp_mov wp_addi CallOk compressAt_ok compressAt_rel)
open VG.Impl.MdStream.X86_64 (compressAt)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Pbkdf2.X86_64 (padLen_ok)
open VG.Proof.Pbkdf2.Md.X86_64.Calls (finG FinArgs rel_taint rel_wp fin_rel restore_ok SavedRegs saveR repr_keep
  PubEq args)
open VG.Proof.Hmac.Generic.Common (bytes_keep bytesAt_take bytesAt_writeBytes_self')
open VG.Proof.Hmac.Common (bytesAt_length xorPad_length writeBytes_at bytesAt_getD')
open VG.Proof.Sha256.Stream (writeBytes writeBytes_frame)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (xorPad ipad opad hmacBlockKey)

variable {H : Hash} (hH : HashOK H)

/-- The registers the code after the inner digest keeps public: `inner`,
the block (its buffer), `out`, `scratch` and the stack pointer. -/
abbrev oregs : List Reg := [.rbx, .rbp, .r13, .r15, .rsp]

/-- The taint checks of the pieces of `finalize` between its calls. -/
structure Checks (H : Hash) : Prop where
  pro : ∃ hc, (Taint.check taint (Taint.ofRegs args) (.block H.stream.finPrologue) hc).isSome = true
  fin1 : ∃ hc, (Taint.check taint (Taint.ofRegs kregs) (.block (fin1Block H.stream)) hc).isSome = true
  mid : ∃ hc, (Taint.check taint (Taint.ofRegs kregs) (.block H.finMid) hc).isSome = true
  out : ∃ hc, (Taint.check taint (Taint.ofRegs oregs) (.block H.finOut) hc).isSome = true

/-- The block: the inner state's buffer. -/
abbrev blk (H : Hash) (s₀ : State) : Addr := inn s₀ + BitVec.ofNat 64 H.P.N

/-- What holds from the outer block on: as `KR`, but `outer` is no longer
needed. -/
structure KO (H : Hash) (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rbx : s.gpr .rbx = inn s₀
  r13 : s.gpr .r13 = op s₀
  r15 : s.gpr .r15 = scr s₀
  saved : SavedRegs H.stream (scr s₀) s₀ s.mem
  ret : s.mem.readW (s₀.gpr .rsp) 64 = s₀.mem.readW (s₀.gpr .rsp) 64

theorem KO.keep {s₀ s s' : State} (h : KO H s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r ∈ [Reg.rbx, .r13, .r15, .rsp], s'.gpr r = s.gpr r) {rs : List Region}
    (hf : Frame rs s.mem s'.mem) (hs : ∀ r ∈ rs, (saveR H.stream (scr s₀)).Disjoint r)
    (hr : ∀ r ∈ rs, (retR s₀).Disjoint r) : KO H s₀ s' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, (hg _ (by simp)).trans h.rsp, (hg _ (by simp)).trans h.rbx,
    (hg _ (by simp)).trans h.r13, (hg _ (by simp)).trans h.r15, h.saved.frame H.stream hf hs,
    (hf.readW (r := retR s₀) (Region.contains_self _ _) hr (by decide)).trans h.ret⟩

section
variable {sc : Nat} {s₀ : State} (hp : Pre (H := H.stream) sc s₀)
include hH hp

/-- The sizes the proof needs. -/
theorem sizes : H.P.N % 4 = 0 ∧ H.D % 4 = 0 ∧ H.P.L % 4 = 0 ∧ H.P.B % 4 = 0 ∧ H.D + H.P.L + 4 ≤ H.P.B ∧
    0 < H.D ∧ H.D ≤ H.P.N ∧ H.P.N + H.P.L ≤ H.P.B ∧ H.P.B ≤ 128 ∧ H.P.so + 96 + H.P.N ≤ 8 * sc ∧
    8 * sc ≤ 2 ^ 64 ∧ H.P.N + H.P.B ≤ 256 := by
  obtain hH_hN4 := hH.hN4; have hH_hD4 := hH.hD4; have hH_hL4 := hH.hL4; have hH_hDL := hH.hDL; have hH_hD0 := hH.hD0; have hH_hDN := hH.hDN
  obtain hH_hNL := hH.hNL; have hH_B_le := hH.B_le; have hH_hso := hH.hso; have hp_nw := hp.nw; have hp_hS := hp.hS
  have : H.P.B % 4 = 0 := by rcases hH.dims.B with h | h <;> omega_using [h]
  have f : H.stream.buf + H.P.N ≤ 8 * sc := hp.fits
  have hb : H.stream.buf = 8 * ((H.P.so + 48) / 8) + 48 := rfl
  have hS : H.stream.S = H.P.N + H.P.B := rfl
  omega_using [hH_hN4, hH_hD4, hH_hL4, hH_hDL, hH_hD0, hH_hDN, hH_hNL, hH_B_le, hH_hso, hp_nw, this, f, hb]

omit hH hp in
/-- The ranges of the inner state, which holds the hash value and the block. -/
theorem in_inR {a n : Nat} (h : a + n ≤ H.P.N + H.P.B) :
    Region.Sub ⟨inn s₀ + BitVec.ofNat 64 a, n⟩ (inR (H := H.stream) s₀) :=
  Offset.sub_base _ h

omit hH in
theorem save_inR {a n : Nat} (h : a + n ≤ H.P.N + H.P.B) :
    (saveR H.stream (scr s₀)).Disjoint ⟨inn s₀ + BitVec.ofNat 64 a, n⟩ :=
  (hp.i_s.symm.sub_left (save_sub hp)).sub_right (in_inR h)

omit hH in
theorem ret_inR {a n : Nat} (h : a + n ≤ H.P.N + H.P.B) :
    (retR s₀).Disjoint ⟨inn s₀ + BitVec.ofNat 64 a, n⟩ :=
  hp.ret_i.sub_right (in_inR h)

omit hH in
/-- `KO` from `KR`, after code that writes only the inner state. -/
theorem KO.of_kr {s s' : State} (hk : KR (H := H.stream) s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r ∈ [Reg.rbx, .r13, .r15, .rsp], s'.gpr r = s.gpr r)
    (hf : Frame [inR (H := H.stream) s₀] s.mem s'.mem) : KO H s₀ s' :=
  KO.keep (s := s) ⟨hk.rd, hk.wr, hk.rsp, hk.rbx, hk.r13, hk.r15, hk.saved, hk.ret⟩ hrd hwr hg hf
    (by simp only [List.mem_singleton]; rintro r rfl; exact hp.i_s.symm.sub_left (save_sub hp))
    (by simp only [List.mem_singleton]; rintro r rfl; exact hp.ret_i)

/-- The outer hash value over the inner state's, the inner digest into its
buffer and the padding after it, and the block's address in `rsi`. -/
theorem mid_ok {s : State} (hk : KR (H := H.stream) s₀ s) :
    WP isa (.block H.finMid) s fun t => KO H s₀ t ∧ t.gpr .rbp = blk H s₀ ∧ t.gpr .rsi = blk H s₀ ∧
      (∀ i < H.P.N, t.mem (inn s₀ + BitVec.ofNat 64 i) = s.mem (outer s₀ + BitVec.ofNat 64 i)) ∧
      bytesAt t.mem (blk H s₀) H.D = bytesAt s.mem (T (H := H.stream) s₀) H.D ∧
      bytesAt t.mem (blk H s₀ + BitVec.ofNat 64 H.D) (H.P.B - H.D) = hH.md.tailPad H.D := by
  obtain ⟨hN4, hD4, hL4, hB4, hDL, hD0, hDN, hNL, hB, -, h8, hSB⟩ := sizes hH hp
  have hS : H.stream.S = H.P.N + H.P.B := rfl
  have hbuf : H.stream.buf + H.P.N ≤ 8 * sc := hp.fits
  obtain ⟨sR, iR, _⟩ := wr_mem hp
  obtain oR : outerR (H := H.stream) s₀ ∈ s.rd ++ s.wr := by rw [hk.rd, hp.rd]; simp
  have z : ∀ p : Addr, p + BitVec.ofNat 64 0 = p := BitVec.add_zero
  obtain tsub : Region.Sub ⟨T (H := H.stream) s₀, H.D⟩ (scR sc s₀) := Offset.sub_base _ (by omega_using [hbuf, hDN])
  simp only [Hash.finMid, List.append_assoc]
  refine copyW_ok (src := .r12) (dst := .rbx) (by decide) (by decide) _ 0 0 H.P.N hN4 _ s _
    (fun a w _ h => by
      rw [hk.r12, add_ofNat]
      exact ⟨_, oR, Offset.contains_base _ (by omega_using [h, hS]) (by omega_using [h, hB, hNL])⟩)
    (fun a w _ h => by
      rw [hk.rbx, add_ofNat, hk.wr]
      exact ⟨_, iR, Offset.contains_base _ (by omega_using [hS, h]) (by omega_using [hSB, h])⟩)
    (by
      rw [hk.r12, hk.rbx]
      exact hp.i_o.symm.sep (Offset.contains_base _ (by omega_using [hS]) (by omega_using []))
        (Offset.contains_base _ (by omega_using [hS]) (by omega_using [])))
    (by omega_using [hB, hNL]) fun s₁ g₁ rd₁ wr₁ m₁ => ?_
  rw [hk.r12, hk.rbx, z, z] at m₁
  obtain r15 : s₁.gpr .r15 = scr s₀ := by rw [g₁ _ (by decide), hk.r15]
  obtain rbx : s₁.gpr .rbx = inn s₀ := by rw [g₁ _ (by decide), hk.rbx]
  refine copyW_ok (src := .r15) (dst := .rbx) (by decide) (by decide) _ H.stream.buf H.P.N H.D hD4 _ s₁ _
    (fun a w hw h => by
      rw [r15, add_ofNat, rd₁, wr₁, hk.rd, hk.wr]
      exact ⟨_, List.mem_append_right _ sR, Offset.contains_base _ (by omega_using [h, hbuf, hDN]) (by omega_using [hw, h, hbuf, h8, hDN])⟩)
    (fun a w _ h => by
      rw [rbx, add_ofNat, wr₁, hk.wr]
      exact ⟨_, iR, Offset.contains_base _ (by omega_using [h, hS, hDL]) (by omega_using [h, hB, hNL, hDL])⟩)
    (by
      rw [r15, rbx]
      exact hp.i_s.symm.sep (Offset.contains_base _ (by omega_using [hDN, hbuf]) (by omega_using [hbuf, h8, hDN, hD0]))
        (Offset.contains_base _ (by omega_using [hS, hDL]) (by omega_using [hB, hNL])))
    (by omega_using [hB, hDL]) fun s₂ g₂ rd₂ wr₂ m₂ => ?_
  rw [r15, rbx] at m₂
  simp only [List.cons_append, List.nil_append]
  refine wp_mov fun s₃ u₃ _ _ => wp_addi fun s₄ u₄ => ?_
  obtain rbp₄ : s₄.gpr .rbp = blk H s₀ := by
    rw [u₄.gpr, u₃.gpr, g₂ _ (by decide), rbx, sx_ofNat (by omega_using [hB, hNL])]
  obtain G₄ : ∀ r, r ≠ .rax → r ≠ .rbp → s₄.gpr r = s₁.gpr r := fun r h1 h2 => by
    rw [u₄.other r h2, u₃.other r h2, g₂ r h1]
  obtain hB16 : H.P.B % 16 = 0 := by rcases hH.dims.B with h | h <;> omega_using [h]
  refine padSel_ok hH.shape (hH.lenOk _ (by omega_using [hB, hDL])) hD4 hB16 hH.dims.L hL4 hH.hPad
    (by omega_using [hDL]) hB (s := s₄) rbp₄
    (by rw [G₄ _ (by decide) (by decide), rbx, add_ofNat,
      show H.P.N + (H.P.B - H.P.L) = H.P.N + H.P.B - H.P.L by omega_using [hDL]])
    (fun a n h' => by
      rw [u₄.wr, u₃.wr, wr₂, wr₁, hk.wr, add_ofNat]
      exact ⟨_, iR, Offset.contains_base _ (by omega_using [h', hS]) (by omega_using [h', hB, hNL])⟩) fun s₅ g₅ rd₅ wr₅ f₅ p₅ d₅ => ?_
  refine wp_mov fun s₆ u₆ _ _ => WP.block_nil ?_
  obtain G : ∀ r, r ≠ .rax → r ≠ .rbp → r ≠ .r12 → r ≠ .rsi → s₆.gpr r = s.gpr r := fun r h1 h2 h3 h4 => by
    rw [u₆.other r h4, g₅ r h1 h3, G₄ r h1 h2, g₁ r h1]
  have hm : s₆.mem = s₅.mem := u₆.mem
  -- What each piece writes.
  obtain f₁ : Frame [⟨inn s₀, H.P.N⟩] s.mem s₁.mem := by
    rw [m₁]; exact writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  obtain f₂ : Frame [⟨blk H s₀, H.D⟩] s₁.mem s₂.mem := by
    rw [m₂]; exact writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  obtain f₄ : s₄.mem = s₂.mem := by rw [u₄.mem, u₃.mem]
  rw [f₄] at f₅ d₅
  obtain fI : Frame [inR (H := H.stream) s₀] s.mem s₆.mem := by
    rw [hm]
    refine ((f₁.sub fun r hr => ?_).trans (f₂.sub fun r hr => ?_)).trans (f₅.sub fun r hr => ?_) <;>
      simp only [List.mem_singleton] at hr <;> subst hr
    · exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega_using [hS])⟩
    · exact ⟨_, List.mem_singleton_self _, in_inR (by omega_using [hDL])⟩
    · exact ⟨_, List.mem_singleton_self _, in_inR (by omega_using [])⟩
  refine ⟨KO.of_kr hp hk (by rw [u₆.rd, rd₅, u₄.rd, u₃.rd, rd₂, rd₁])
      (by rw [u₆.wr, wr₅, u₄.wr, u₃.wr, wr₂, wr₁])
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> exact G _ (by decide) (by decide) (by decide) (by decide)) fI,
    by rw [u₆.other _ (by decide), g₅ _ (by decide) (by decide), rbp₄],
    by rw [u₆.gpr, g₅ _ (by decide) (by decide), rbp₄], fun i hi => ?_, ?_, by rw [hm]; exact p₅⟩
  · -- The hash value: the outer one, which the later pieces keep.
    obtain hd : ∀ {a n : Nat}, H.P.N ≤ a → a + n ≤ H.P.N + H.P.B →
        ∀ r ∈ [(⟨inn s₀ + BitVec.ofNat 64 a, n⟩ : Region)], Region.Disjoint ⟨inn s₀, H.P.N⟩ r := fun ha hn => by
      simp only [List.mem_singleton]; rintro r rfl; exact Offset.base_disjoint _ ha (by omega_using [hn, hB, hNL])
    rw [hm, f₅.bytes (R := ⟨inn s₀, H.P.N⟩) (hd (Nat.le_refl _) (by omega_using [])) (by show H.P.N ≤ 2 ^ 64; omega_using [hB, hNL]) hi,
      f₂.bytes (R := ⟨inn s₀, H.P.N⟩) (hd (Nat.le_refl _) (by omega_using [hDL])) (by show H.P.N ≤ 2 ^ 64; omega_using [hB, hNL]) hi,
      m₁, writeBytes_at _ _ _ (by rw [bytesAt_length]; exact hi) (by rw [bytesAt_length]; omega_using [hB, hNL]),
      bytesAt_getD' _ _ hi]
  · -- The inner digest.
    rw [hm, d₅, m₂, bytesAt_writeBytes_self' (bytesAt_length _ _ _) (by omega_using [hB, hDL])]
    exact bytes_keep f₁ (by
      simp only [List.mem_singleton]; rintro r rfl
      exact (hp.i_s.sub_right tsub).symm.sub_right (Region.sub_prefix (by omega_using [hS]))) (by omega_using [hB, hDL])

/-- What the call of the compression function needs. -/
theorem callOk {t : State} (hk : KO H s₀ t) (hsi : t.gpr .rsi = blk H s₀) :
    CallOk H.P t (inn s₀) (scr s₀) (blk H s₀) := by
  obtain ⟨hN4, hD4, hL4, hB4, hDL, hD0, hDN, hNL, hB, hf, h8, hSB⟩ := sizes hH hp
  have hH_hso := hH.hso
  have hS : H.stream.S = H.P.N + H.P.B := rfl
  obtain ⟨sR, iR, _⟩ := wr_mem hp
  obtain z : inn s₀ + BitVec.ofNat 64 0 = inn s₀ := BitVec.add_zero _
  obtain hv : Region.Sub ⟨inn s₀, H.P.N⟩ (inR (H := H.stream) s₀) := Region.sub_prefix (by omega_using [hS])
  obtain hb : Region.Sub ⟨blk H s₀, H.P.B⟩ (inR (H := H.stream) s₀) := in_inR (by omega_using [])
  obtain hs : Region.Sub ⟨scr s₀, H.P.so⟩ (scR sc s₀) := Region.sub_prefix (by omega_using [hf])
  obtain b8 : Region.Sub (below (t.gpr .rsp) 8) (stkR s₀) := by
    rw [hk.rsp]; exact Offset.sub_below _ (by omega_using []) (by omega_using [])
  refine ⟨hk.rbx, hk.r15, hsi, (hp.i_s.sub_left hv).sub_right hs, Offset.disjoint_base _ (Nat.le_refl _) (by omega_using [hB, hNL]),
    (hp.i_s.sub_left hb).sub_right hs, (hp.stk_i.sub_left b8).sub_right hv, (hp.stk_s.sub_left b8).sub_right hs,
    (hp.stk_i.sub_left b8).sub_right hb, ?_, ?_⟩
  · rw [hk.rd, hk.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_append_right _ iR, H.P.N, rfl, by show H.P.N + H.P.B ≤ H.P.N + H.P.B; omega_using []⟩
    · exact ⟨_, List.mem_append_right _ iR, 0, z.symm, by show 0 + H.P.N ≤ H.P.N + H.P.B; omega_using []⟩
    · exact ⟨_, List.mem_append_right _ sR, 0, (BitVec.add_zero _).symm, by show 0 + H.P.so ≤ 8 * sc; omega_using [hf]⟩
  · rw [hk.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, iR, 0, z.symm, by show 0 + H.P.N ≤ H.P.N + H.P.B; omega_using []⟩
    · exact ⟨_, sR, 0, (BitVec.add_zero _).symm, by show 0 + H.P.so ≤ 8 * sc; omega_using [hf]⟩

/-- The compression of the block into the hash value. -/
theorem cmp_ok {t : State} (hk : KO H s₀ t) (hsi : t.gpr .rsi = blk H s₀) {Q : State → Prop}
    (k : ∀ s', KO H s₀ s' → s'.gpr .rbp = t.gpr .rbp →
      hH.md.stateAt s'.mem (inn s₀) = hH.md.compress (hH.md.stateAt t.mem (inn s₀))
        (hH.md.blockAt t.mem (blk H s₀)) → Q s') :
    WP isa (compressAt H.compN H.compC) t Q := by
  obtain ⟨hN4, hD4, hL4, hB4, hDL, hD0, hDN, hNL, hB, hf, h8, hSB⟩ := sizes hH hp
  have hH_hso := hH.hso
  have hS : H.stream.S = H.P.N + H.P.B := rfl
  obtain z : inn s₀ + BitVec.ofNat 64 0 = inn s₀ := BitVec.add_zero _
  refine compressAt_ok hH.md hH.comp (callOk hH hp hk hsi) (by omega_using [hB]) (by omega_using [hB, hNL])
    fun s' hrd hwr hcs hfr hst _ _ => k s' (hk.keep hrd hwr (fun r hr => hcs r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> simp [calleeSaved])) hfr ?_ ?_)
    (hcs _ (by simp [calleeSaved])) hst
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · have := save_inR hp (a := 0) (n := H.P.N) (by omega_using []); rwa [z] at this
    · exact (cal_save hH.stream hp).symm.sub_right (Region.sub_prefix (by show H.P.so ≤ H.P.so + 48; omega_using []))
    · rw [hk.rsp]
      exact (hp.stk_s.symm.sub_left (save_sub hp)).sub_right (Offset.sub_below _ (by omega_using []) (by omega_using []))
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact hp.ret_i.sub_right (Region.sub_prefix (by show H.P.N ≤ H.P.N + H.P.B; omega_using []))
    · exact hp.ret_s.sub_right (Region.sub_prefix (by omega_using [hf]))
    · rw [hk.rsp]; exact (stk_ret (s₀ := s₀)).symm.sub_right (Offset.sub_below _ (by omega_using []) (by omega_using []))

/-- The MAC to `out`, and our caller's registers back. -/
theorem out_ok {s : State} (hk : KO H s₀ s) (hbp : s.gpr .rbp = blk H s₀) :
    WP isa (.block H.finOut) s fun s' => ∃ t, KO H s₀ t ∧
      bytesAt t.mem (op s₀) H.D = (hH.md.digest (hH.md.stateAt s.mem (inn s₀))).take H.D ∧ s'.mem = t.mem ∧
      (∀ r ∈ [Reg.rbx, .rbp, .r12, .r13, .r14, .r15], s'.gpr r = s₀.gpr r) ∧
      (∀ r, r ∉ [Reg.rbx, .rbp, .r12, .r13, .r14, .r15] → s'.gpr r = t.gpr r) := by
  obtain ⟨hN4, hD4, hL4, hB4, hDL, hD0, hDN, hNL, hB, hf, h8, hSB⟩ := sizes hH hp
  have hD := hp.hD
  have hS : H.stream.S = H.P.N + H.P.B := rfl
  obtain eD : 4 * (H.D / 4) = H.D := by omega_using [hD4]
  obtain ⟨sR, iR, pR⟩ := wr_mem hp
  have z : ∀ p : Addr, p + BitVec.ofNat 64 0 = p := BitVec.add_zero
  obtain hdl := hH.md.digest_length (hH.md.stateAt s.mem (inn s₀))
  obtain hL : 8 * H.stream.W + 48 ≤ 8 * sc := by
    have : H.stream.buf = 8 * H.stream.W + 48 := rfl
    have hp_fits := hp.fits
    omega_using [hp_fits, this]
  obtain fin : ∀ t, KO H s₀ t → bytesAt t.mem (op s₀) H.D = (hH.md.digest (hH.md.stateAt s.mem (inn s₀))).take H.D →
      WP isa (.block H.stream.restore) t fun s' => ∃ t, KO H s₀ t ∧
        bytesAt t.mem (op s₀) H.D = (hH.md.digest (hH.md.stateAt s.mem (inn s₀))).take H.D ∧ s'.mem = t.mem ∧
        (∀ r ∈ [Reg.rbx, .rbp, .r12, .r13, .r14, .r15], s'.gpr r = s₀.gpr r) ∧
        (∀ r, r ∉ [Reg.rbx, .rbp, .r12, .r13, .r14, .r15] → s'.gpr r = t.gpr r) := fun t kt bt =>
    WP.mono (restore_ok H.stream kt.r15 hp.hW kt.saved (by rw [kt.wr]; exact sR) hL)
      fun s' ⟨hm, _, _, hg, ho⟩ => ⟨t, kt, bt, hm, hg, ho⟩
  obtain rbx_in : InRegions (s.rd ++ s.wr) (s.gpr .rbx) H.P.N := by
    have := Offset.contains_base (inn s₀) (d := 0) (n := H.P.N) (k := H.P.N + H.P.B) (by omega_using []) (by omega_using [])
    rw [z] at this
    rw [hk.rbx, hk.rd, hk.wr]
    exact ⟨_, List.mem_append_right _ iR, this⟩
  unfold Hash.finOut
  by_cases hDN' : H.D < H.P.N
  · simp only [hDN', ↓reduceIte, List.append_assoc]
    rw [WP.block_append_iff]
    refine WP.mono (hH.shape.out s rbx_in (by
        rw [hbp, hk.wr]; exact ⟨_, iR, Offset.contains_base _ (by omega_using [hS, hNL]) (by omega_using [hB, hNL])⟩)
      (by rw [hk.rbx, hbp]; exact Offset.base_disjoint _ (Nat.le_refl _) (by omega_using [hB, hNL])))
      fun s₁ ⟨g₁, rd₁, wr₁, m₁⟩ => ?_
    rw [hbp, hk.rbx] at m₁
    obtain f₁ : Frame [⟨blk H s₀, H.P.N⟩] s.mem s₁.mem := by
      rw [m₁]; exact writeBytes_frame _ _ _ (by rw [hdl]; exact Region.contains_self _ _)
    obtain k₁ : KO H s₀ s₁ := hk.keep rd₁ wr₁ (fun r hr => g₁ r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> decide)) f₁
      (by simp only [List.mem_singleton]; rintro r rfl; exact save_inR hp (by omega_using [hNL]))
      (by simp only [List.mem_singleton]; rintro r rfl; exact ret_inR hp (by omega_using [hNL]))
    obtain b₁ : bytesAt s₁.mem (blk H s₀) H.D = (hH.md.digest (hH.md.stateAt s.mem (inn s₀))).take H.D := by
      rw [bytesAt_take _ _ (Nat.le_of_lt hDN'), m₁, bytesAt_writeBytes_self' hdl (by omega_using [hSB])]
    obtain rbp₁ : s₁.gpr .rbp = blk H s₀ := by rw [g₁ _ (by decide), hbp]
    refine copyW_ok (src := .rbp) (dst := .r13) (by decide) (by decide) _ 0 0 H.D hD4 _ s₁ _
      (fun a w hw h => by
        rw [rbp₁, add_ofNat, add_ofNat, rd₁, wr₁, hk.rd, hk.wr]
        exact ⟨_, List.mem_append_right _ iR, Offset.contains_base _ (by omega_using [h, hS, hDL]) (by omega_using [hw, h, hB, hNL, hDL])⟩)
      (fun a w hw h => by
        rw [k₁.r13, add_ofNat, k₁.wr]
        exact ⟨_, pR, Offset.contains_base _ (by show 0 + a + w ≤ H.D; omega_using [h]) (by omega_using [hw, h, hB, hDL])⟩)
      (by
        rw [rbp₁, k₁.r13, add_ofNat]
        exact hp.i_p.sep (Offset.contains_base _ (by omega_using [hS, hDL]) (by omega_using [hB, hNL]))
          (Offset.contains_base _ (by show 0 + H.D ≤ H.D; omega_using []) (by omega_using [])))
      (by omega_using [hB, hDL]) fun s₂ g₂ rd₂ wr₂ m₂ => ?_
    rw [rbp₁, k₁.r13, z, z] at m₂
    refine fin s₂ (k₁.keep rd₂ wr₂ (fun r hr => g₂ r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> decide))
      (m₂ ▸ writeBytes_frame _ _ _ (R := opR (H := H.stream) s₀) (by
        rw [bytesAt_length]; exact Region.contains_self _ _))
      (by simp only [List.mem_singleton]; rintro r rfl; exact hp.p_s.symm.sub_left (save_sub hp))
      (by simp only [List.mem_singleton]; rintro r rfl; exact hp.ret_p)) ?_
    rw [m₂, bytesAt_writeBytes_self' (bytesAt_length _ _ _) (by omega_using [hB, hDL]), b₁]
  · have eDN : H.D = H.P.N := by omega_using [hDN', hDN]
    simp only [hDN', ↓reduceIte, List.cons_append]
    refine wp_mov fun s₁ u₁ _ _ => ?_
    rw [WP.block_append_iff]
    obtain rbx₁ : s₁.gpr .rbx = inn s₀ := by rw [u₁.other _ (by decide), hk.rbx]
    refine WP.mono (hH.shape.out s₁ (by rw [u₁.rd, u₁.wr, u₁.other _ (by decide)]; exact rbx_in) (by
        rw [u₁.gpr, hk.r13, u₁.wr, hk.wr, ← eDN]; exact ⟨_, pR, Region.contains_self _ _⟩)
      (by rw [rbx₁, u₁.gpr, hk.r13, ← eDN]; exact hp.i_p.sub_left (Region.sub_prefix (by omega_using [hS, hDL]))))
      fun s₂ ⟨g₂, rd₂, wr₂, m₂⟩ => ?_
    rw [rbx₁, u₁.gpr, hk.r13, u₁.mem] at m₂
    refine fin s₂ (hk.keep (rd₂.trans u₁.rd) (wr₂.trans u₁.wr) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> rw [g₂ _ (by decide), u₁.other _ (by decide)])
      (m₂ ▸ writeBytes_frame _ _ _ (R := opR (H := H.stream) s₀) (by
        rw [hdl, ← eDN]; exact Region.contains_self _ _))
      (by simp only [List.mem_singleton]; rintro r rfl; exact hp.p_s.symm.sub_left (save_sub hp))
      (by simp only [List.mem_singleton]; rintro r rfl; exact hp.ret_p)) ?_
    rw [m₂, eDN, bytesAt_writeBytes_self' hdl (by omega_using [hB, hNL]), List.take_of_length_le (by omega_using [hdl])]

/-! ## Correctness -/

theorem correct : WP isa H.hmacFin s₀ fun s' => gprPreserved s₀ s' ∧ (finG hH.SH sc).post s₀ s' := by
  obtain ⟨hN4, hD4, hL4, hB4, hDL, hD0, hDN, hNL, hB, hf, h8, hSB⟩ := sizes hH hp
  have hB0 := hH.B_pos
  refine WP.seq (WP.mono (pro_ok hp) fun s₁ ⟨k₁, di₁, dx₁, f₁⟩ => ?_)
  refine WP.seq (WP.seq (WP.mono (fin1Args_ok hH.stream hp k₁ di₁ dx₁) fun t₁ ⟨kt₁, a₁, si₁, m₁⟩ =>
    finCall_ok hH.stream hp kt₁ a₁ fun s₂ k₂ f₂ d₂ => ?_))
  refine WP.seq (WP.mono (mid_ok hH hp k₂) fun s₃ ⟨k₃, bp₃, si₃, i₃, b₃, p₃⟩ => ?_)
  refine WP.seq (cmp_ok hH hp k₃ si₃ fun s₄ k₄ bp₄ e₄ => ?_)
  refine WP.mono (out_ok hH hp k₄ (bp₄.trans bp₃)) fun s' ⟨s₅, k₅, m₅, hm, hg, ho⟩ =>
    ⟨⟨fun r hr => ?_, by rw [hm, k₅.ret]⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hg _ (by simp)
    · exact hg _ (by simp)
    · rw [ho _ (by simp), k₅.rsp]
    · exact hg _ (by simp)
    · exact hg _ (by simp)
    · exact hg _ (by simp)
    · exact hg _ (by simp)
  -- The functional part.
  intro k0 text hk0 hlen hrI hcnt hrO
  rw [hH.hB] at hk0 hcnt
  obtain hl0 : (xorPad k0 ipad ++ text).length = H.P.B + text.length := by
    rw [List.length_append, xorPad_length, hk0]
  -- The outer state is untouched until the inner digest is written.
  obtain oI : ∀ r ∈ [saveR H.stream (scr s₀)], Region.Disjoint (outerR (H := H.stream) s₀) r := by
    simp only [List.mem_singleton]; rintro r rfl; exact hp.o_s.sub_right (save_sub hp)
  obtain o₂ : ∀ r ∈ [inR (H := H.stream) s₀, tR (H := H.stream) s₀, calR hH.stream s₀,
      stkR s₀], Region.Disjoint (outerR (H := H.stream) s₀) r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact hp.i_o.symm
    · exact hp.o_s.sub_right (t_sub hp)
    · exact hp.o_s.sub_right (cal_sub hH.stream hp)
    · exact hp.stk_o.symm
  obtain rO₂ := repr_keep hH.stream f₂ o₂ (m₁ ▸ repr_keep hH.stream f₁ oI hrO)
  -- The inner digest.
  obtain dig : (bytesAt s₂.mem (T (H := H.stream) s₀) H.P.N).take H.D = hH.SH.H.hash (xorPad k0 ipad ++ text) :=
    d₂ _ (m₁ ▸ repr_keep hH.stream f₁ (by
      simp only [List.mem_singleton]; rintro r rfl; exact hp.i_s.sub_right (save_sub hp)) hrI)
    (by rw [hl0]; rw [hk0] at hlen; exact hlen)
    (by rw [si₁, hcnt, hl0])
  -- The outer hash: one compression of the outer hash value.
  obtain hxl : (xorPad k0 opad).length = H.P.B := by rw [xorPad_length, hk0]
  obtain ho : hH.md.stateAt s₃.mem (inn s₀) = hH.md.compressList hH.iv (xorPad k0 opad) 1 := by
    rw [hH.reloc s₂.mem s₃.mem (outer s₀) (inn s₀) i₃]
    exact Md.stateAt_of_repr hB0 hxl ((hH.repr _ _ _).1 rO₂)
  show bytesAt s'.mem (op s₀) hH.SH.digestBytes = hmacBlockKey hH.SH.H k0 text
  rw [hH.hD, hm, m₅, e₄, ho, hH.md.blockAt_eq (by omega_using [hDL]) p₃, b₃, hmacBlockKey, ← dig,
    ← bytesAt_take _ _ hDN, hH.iterOk.link.hash_block hxl (bytesAt_length _ _ _)]

end

/-! ## Constant time -/

section

variable {sc : Nat} {s₀ s₀' : State} (hp : Pre (H := H.stream) sc s₀) (hp' : Pre (H := H.stream) sc s₀')
  (hq : PubEq s₀ s₀')

omit hH in
/-- The registers `oregs` agree in two runs. -/
theorem ko_agree (hq : PubEq s₀ s₀') {s s' : State} (h : KO H s₀ s ∧ s.gpr .rbp = blk H s₀)
    (h' : KO H s₀' s' ∧ s'.gpr .rbp = blk H s₀') : ∀ r ∈ oregs, s.gpr r = s'.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [h.1.rbx, h'.1.rbx, inn, inn, hq.rdi]
  · rw [h.2, h'.2, blk, blk, inn, inn, hq.rdi]
  · rw [h.1.r13, h'.1.r13, op, op, hq.rcx]
  · rw [h.1.r15, h'.1.r15, scr, scr, hq.r8]
  · rw [h.1.rsp, h'.1.rsp, hq.rsp]

include hH hp hp' hq

theorem ct (hc : Checks H) : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') H.hmacFin fun _ _ => True := by
  obtain pro : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') (.block H.stream.finPrologue)
      fun s s' => (KR (H := H.stream) s₀ s ∧ s.gpr .rdi = inn s₀ ∧ s.gpr .rdx = s₀.gpr .rdx) ∧
        (KR (H := H.stream) s₀' s' ∧ s'.gpr .rdi = inn s₀' ∧ s'.gpr .rdx = s₀'.gpr .rdx) :=
    rel_taint args (fun s s' e e' r hr => by
        rw [e, e']
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
        · exact hq.rdi
        · exact hq.rsi
        · exact hq.rdx
        · exact hq.rcx
        · exact hq.r8
        · exact hq.rsp) hc.pro
      (fun _ e => by rw [e]; exact WP.mono (pro_ok hp) fun _ ⟨k, d, x, _⟩ => ⟨k, d, x⟩)
      (fun _ e => by rw [e]; exact WP.mono (pro_ok hp') fun _ ⟨k, d, x, _⟩ => ⟨k, d, x⟩)
  obtain fin1 := fin_rel' hH.stream hp hp' hq (c := s₀.gpr .rdx)
    (F := fun s => KR (H := H.stream) s₀ s ∧ s.gpr .rdi = inn s₀ ∧ s.gpr .rdx = s₀.gpr .rdx)
    (F' := fun s => KR (H := H.stream) s₀' s ∧ s.gpr .rdi = inn s₀' ∧ s.gpr .rdx = s₀'.gpr .rdx) hc.fin1
    (fun _ _ h h' => kr_agree hq h.1 h'.1)
    (fun s ⟨k, d, x⟩ => fin1Args_ok hH.stream hp k d x)
    (fun s ⟨k, d, x⟩ => WP.mono (fin1Args_ok hH.stream hp' k d x) fun _ ⟨k, a, si, m⟩ =>
      ⟨k, a, si.trans hq.rdx.symm, m⟩)
  obtain mid : RelCT isa (fun s s' => KR (H := H.stream) s₀ s ∧ KR (H := H.stream) s₀' s') (.block H.finMid)
      fun s s' => (KO H s₀ s ∧ s.gpr .rbp = blk H s₀ ∧ s.gpr .rsi = blk H s₀) ∧
        (KO H s₀' s' ∧ s'.gpr .rbp = blk H s₀' ∧ s'.gpr .rsi = blk H s₀') :=
    rel_taint kregs (fun _ _ h h' => kr_agree hq h h') hc.mid
      (fun s k => WP.mono (mid_ok hH hp k) fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩)
      (fun s k => WP.mono (mid_ok hH hp' k) fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩)
  obtain cmp : RelCT isa (fun s s' => (KO H s₀ s ∧ s.gpr .rbp = blk H s₀ ∧ s.gpr .rsi = blk H s₀) ∧
        (KO H s₀' s' ∧ s'.gpr .rbp = blk H s₀' ∧ s'.gpr .rsi = blk H s₀')) (compressAt H.compN H.compC)
      fun s s' => (KO H s₀ s ∧ s.gpr .rbp = blk H s₀) ∧ (KO H s₀' s' ∧ s'.gpr .rbp = blk H s₀') :=
    rel_wp (compressAt_rel hH.md hH.comp fun s s' ⟨⟨k, _, si⟩, ⟨k', _, si'⟩⟩ =>
        ⟨⟨_, _, _, callOk hH hp k si⟩, ⟨_, _, _, callOk hH hp' k' si'⟩,
          by rw [k.rbx, k'.rbx, inn, inn, hq.rdi], by rw [k.r15, k'.r15, scr, scr, hq.r8],
          by rw [si, si', blk, blk, inn, inn, hq.rdi], by rw [k.rsp, k'.rsp, hq.rsp]⟩)
      (fun s ⟨k, bp, si⟩ => cmp_ok hH hp k si fun s' k' bp' _ => ⟨k', bp'.trans bp⟩)
      (fun s ⟨k, bp, si⟩ => cmp_ok hH hp' k si fun s' k' bp' _ => ⟨k', bp'.trans bp⟩)
  obtain ⟨_, hr⟩ := hc.out
  obtain out : RelCT isa (fun s s' => (KO H s₀ s ∧ s.gpr .rbp = blk H s₀) ∧ (KO H s₀' s' ∧ s'.gpr .rbp = blk H s₀'))
      (.block H.finOut) fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs oregs) (fun _ _ h => Taint.agree_ofRegs (ko_agree hq h.1 h.2)) hr
  exact pro.seq (fin1.seq (mid.seq (cmp.seq out)))

end

/-- HMAC's `finalize` is verified against `finG`, given the taint checks and
the facts about its code that the kernel checks for each hash function. -/
theorem verified {sc : Nat} (hc : Checks H) (hfit : H.stream.buf + H.stream.F ≤ 8 * sc)
    (hmx : H.hmacFin.allInstrs (fun i => !loadsMxcsr i) = true) (hsat : ∃ s, (finG hH.SH sc).pre s) :
    Verified X86_64.target H.hmacFin (finG hH.SH sc) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, hsat⟩
  · obtain ⟨t, s', he, hg, hpost⟩ := correct hH (pre_of hH.stream sc hs hfit)
    exact ⟨t, s', he, abiPreserved_of_exec hmx he hg, hpost⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hpub
    exact (ct hH (pre_of hH.stream sc h₁ hfit) (pre_of hH.stream sc h₂ hfit) ⟨h1, h2, h3, h4, h5, h6⟩ hc
      _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.Pbkdf2.Md.X86_64.HmacFin

end

end


/-!
# HMAC and PBKDF2-HMAC over any Merkle–Damgård hash function on x86-64: the functions, verified

What the kernel checks of a hash function's code does not depend on its
compression function or its streaming `init`, which our functions only call:
`core H` is `H` with both replaced by empty code, and the facts about every
instruction of `H`'s functions follow from those about `core H` and about the
two callees (`core_pbkdf2`, …). `CoreOK` is what the kernel checks of `core
H`, once for each hash function; `Callees` is what each implementation of the
compression function brings. From them, HMAC's `init` and `finalize`,
`iterate` and `pbkdf2` are verified against the shared contracts of
`Spec/Hmac/Generic.lean` and `Spec/Pbkdf2/Generic.lean`.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Md.X86_64

open VG.X86_64
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Pbkdf2.Md.X86_64.Calls (initG finG)
open VG.Proof.Pbkdf2.X86_64 (iterK iterImp)

/-- No instruction of `c` writes `rsp`, from a check that runs in the kernel. -/
theorem nosp_of {c : Prog isa} (h : c.allInstrs (fun i => !Taint.clobbers i .rsp) = true) : NoSp c :=
  fun i hi => by
    obtain h' := List.all_eq_true.mp ((Code.allInstrs_eq _ c) ▸ h) i hi
    revert h'; cases Taint.clobbers i .rsp <;> simp

/-- What stands for `compBoth` in `core`: a call, as `compBoth` is but for
the instructions that set up its arguments. -/
def coreBoth : Prog isa := .call "" (.block [])

/-- `H` without the functions it calls: its own code. -/
def core (H : Hash) : Hash := ⟨H.P, H.D, H.W, "", .block [], "", .block [], "", "", "", "", "", coreBoth⟩

/-! ## Every instruction, from the own code and the callees' -/

section
variable {H : Hash} {p : Instr → Bool} (hc : H.compC.allInstrs p = true) (hi : H.initC.allInstrs p = true)
include hc hi

theorem core_pbkdf2 (hb : H.compBoth.allInstrs p = true) (h : (core H).pbkdf2.allInstrs p = true) :
    H.pbkdf2.allInstrs p = true := by
  simp only [Hash.pbkdf2, Hash.key, Hash.hashKey, Hash.setup, Hash.block, Hash.outLen, Hash.outLoop,
    Hash.hmacInit, Hash.initKeys, Hash.hmacFin, Hash.iterate, Impl.Pbkdf2.X86_64.iterate, Impl.Pbkdf2.X86_64.body,
    Impl.Pbkdf2.X86_64.compressBlock, Hash.updC, Hash.finC, Hash.stream,
    Impl.Pbkdf2.Md.X86_64.Stream.callInit, Impl.Pbkdf2.Md.X86_64.Stream.callFin,
    Impl.MdStream.X86_64.update, Impl.MdStream.X86_64.updateBody, Impl.MdStream.X86_64.updateTail,
    Impl.MdStream.X86_64.compressN, Impl.MdStream.X86_64.compressAt, Impl.MdStream.X86_64.compressWith,
    Impl.MdStream.X86_64.finalize, Impl.MdStream.X86_64.finalizeBody,
    core, coreBoth, Code.allInstrs, hc, hi, hb, Bool.and_true, Bool.true_and] at h ⊢
  exact h

omit hc in
theorem core_hmacInit (hb : H.compBoth.allInstrs p = true) (h : (core H).hmacInit.allInstrs p = true) :
    H.hmacInit.allInstrs p = true := by
  simp only [Hash.hmacInit, Hash.initKeys, Hash.stream, Impl.Pbkdf2.Md.X86_64.Stream.callInit,
    core, coreBoth, Code.allInstrs, hi, hb, Bool.and_true, Bool.true_and] at h ⊢
  exact h

omit hi in
theorem core_hmacFin (h : (core H).hmacFin.allInstrs p = true) : H.hmacFin.allInstrs p = true := by
  simp only [Hash.hmacFin, Hash.finMid, Hash.finOut, Hash.finC, Hash.stream,
    Impl.Pbkdf2.Md.X86_64.Stream.callFin,
    Impl.MdStream.X86_64.compressAt, Impl.MdStream.X86_64.compressWith,
    Impl.MdStream.X86_64.finalize, Impl.MdStream.X86_64.finalizeBody,
    core, Code.allInstrs, hc, Bool.and_true, Bool.true_and] at h ⊢
  exact h

omit hi in
theorem core_iterate (h : (core H).iterate.allInstrs p = true) : H.iterate.allInstrs p = true := by
  simp only [Hash.iterate, Impl.Pbkdf2.X86_64.iterate, Impl.Pbkdf2.X86_64.body,
    Impl.Pbkdf2.X86_64.compressBlock, Impl.MdStream.X86_64.compressAt, Impl.MdStream.X86_64.compressWith,
    core, Code.allInstrs, hc, Bool.and_true, Bool.true_and] at h ⊢
  exact h

omit hi in
theorem core_updC (h : (core H).updC.allInstrs p = true) : H.updC.allInstrs p = true := by
  simp only [Hash.updC, Impl.MdStream.X86_64.update, Impl.MdStream.X86_64.updateBody,
    Impl.MdStream.X86_64.updateTail, Impl.MdStream.X86_64.compressN, Impl.MdStream.X86_64.compressWith,
    core, Code.allInstrs, hc, Bool.and_true, Bool.true_and] at h ⊢
  exact h

omit hi in
theorem core_finC (h : (core H).finC.allInstrs p = true) : H.finC.allInstrs p = true := by
  simp only [Hash.finC, Impl.MdStream.X86_64.finalize, Impl.MdStream.X86_64.finalizeBody,
    Impl.MdStream.X86_64.compressAt, Impl.MdStream.X86_64.compressWith,
    core, Code.allInstrs, hc, Bool.and_true, Bool.true_and] at h ⊢
  exact h

end

/-! ## How deeply calls nest -/

section
variable {H : Hash} (hc : H.compC.depth = 0) (hi : H.initC.depth = 0)
include hc hi

omit hc in
theorem core_hmacInit_depth (hb : H.compBoth.depth = 1) (h : (core H).hmacInit.depth ≤ 2) :
    H.hmacInit.depth ≤ 2 := by
  simp only [Hash.hmacInit, Hash.initKeys, Hash.stream, Impl.Pbkdf2.Md.X86_64.Stream.callInit,
    core, coreBoth, Code.depth, hi, hb] at h ⊢
  exact h

omit hi in
theorem core_hmacFin_depth (h : (core H).hmacFin.depth ≤ 2) : H.hmacFin.depth ≤ 2 := by
  simp only [Hash.hmacFin, Hash.finC, Hash.stream, Impl.Pbkdf2.Md.X86_64.Stream.callFin,
    Impl.MdStream.X86_64.compressAt, Impl.MdStream.X86_64.compressWith,
    Impl.MdStream.X86_64.finalize, Impl.MdStream.X86_64.finalizeBody,
    core, Code.depth, hc] at h ⊢
  exact h

omit hi in
theorem core_iterate_depth (h : (core H).iterate.depth ≤ 2) : H.iterate.depth ≤ 2 := by
  simp only [Hash.iterate, Impl.Pbkdf2.X86_64.iterate, Impl.Pbkdf2.X86_64.body,
    Impl.Pbkdf2.X86_64.compressBlock, Impl.MdStream.X86_64.compressAt, Impl.MdStream.X86_64.compressWith,
    core, Code.depth, hc] at h ⊢
  exact h

omit hi in
theorem core_updC_depth (h : (core H).updC.depth ≤ 1) : H.updC.depth ≤ 1 := by
  simp only [Hash.updC, Impl.MdStream.X86_64.update, Impl.MdStream.X86_64.updateBody,
    Impl.MdStream.X86_64.updateTail, Impl.MdStream.X86_64.compressN, Impl.MdStream.X86_64.compressWith,
    core, Code.depth, hc] at h ⊢
  exact h

omit hi in
theorem core_finC_depth (h : (core H).finC.depth ≤ 1) : H.finC.depth ≤ 1 := by
  simp only [Hash.finC, Impl.MdStream.X86_64.finalize, Impl.MdStream.X86_64.finalizeBody,
    Impl.MdStream.X86_64.compressAt, Impl.MdStream.X86_64.compressWith, core, Code.depth, hc] at h ⊢
  exact h

end

/-! ## How much stack HMAC and PBKDF2 use

HMAC's and PBKDF2's own code has no frames: the stack it uses is the return
addresses of the calls it nests, with callees that use none. -/

section
variable {H : Hash} (hc : H.compC.x86_64Depth = 0) (hi : H.initC.x86_64Depth = 0)
include hc hi

omit hc in
theorem core_hmacInit_xdepth (hb : H.compBoth.x86_64Depth = 8) (h : (core H).hmacInit.x86_64Depth ≤ 16) :
    H.hmacInit.x86_64Depth ≤ 16 := by
  simp only [Hash.hmacInit, Hash.initKeys, Hash.stream, Impl.Pbkdf2.Md.X86_64.Stream.callInit,
    core, coreBoth, Code.x86_64Depth, hi, hb] at h ⊢
  exact h

theorem core_pbkdf2_xdepth (hb : H.compBoth.x86_64Depth = 8) (h : (core H).pbkdf2.x86_64Depth ≤ 24) :
    H.pbkdf2.x86_64Depth ≤ 24 := by
  simp only [Hash.pbkdf2, Hash.key, Hash.hashKey, Hash.setup, Hash.block, Hash.outLen, Hash.outLoop,
    Hash.hmacInit, Hash.initKeys, Hash.hmacFin, Hash.iterate, Impl.Pbkdf2.X86_64.iterate, Impl.Pbkdf2.X86_64.body,
    Impl.Pbkdf2.X86_64.compressBlock, Hash.updC, Hash.finC, Hash.stream,
    Impl.Pbkdf2.Md.X86_64.Stream.callInit, Impl.Pbkdf2.Md.X86_64.Stream.callFin,
    Impl.MdStream.X86_64.update, Impl.MdStream.X86_64.updateBody, Impl.MdStream.X86_64.updateTail,
    Impl.MdStream.X86_64.compressN, Impl.MdStream.X86_64.compressAt, Impl.MdStream.X86_64.compressWith,
    Impl.MdStream.X86_64.finalize, Impl.MdStream.X86_64.finalizeBody,
    core, coreBoth, Code.x86_64Depth, hc, hi, hb] at h ⊢
  exact h

omit hi in
theorem core_hmacFin_xdepth (h : (core H).hmacFin.x86_64Depth ≤ 16) : H.hmacFin.x86_64Depth ≤ 16 := by
  simp only [Hash.hmacFin, Hash.finC, Hash.stream, Impl.Pbkdf2.Md.X86_64.Stream.callFin,
    Impl.MdStream.X86_64.compressAt, Impl.MdStream.X86_64.compressWith,
    Impl.MdStream.X86_64.finalize, Impl.MdStream.X86_64.finalizeBody,
    core, Code.x86_64Depth, hc] at h ⊢
  exact h

end

/-! ## The taint checks, which look only at the own code -/

theorem HmacInit.Checks.of_core {H : Hash} (h : HmacInit.Checks (core H)) : HmacInit.Checks H :=
  ⟨h.pro, h.argI, h.keys, h.mid, h.restore⟩

theorem HmacFin.Checks.of_core {H : Hash} (h : HmacFin.Checks (core H)) : HmacFin.Checks H :=
  ⟨h.pro, h.fin1, h.mid, h.out⟩

theorem Pbk.Checks.of_core {H : Hash} (h : Pbk.Checks (core H)) : Pbk.Checks H :=
  ⟨h.load, h.entry, h.hk1, h.hk3, h.hk5, h.hk7, h.short, h.su1, h.su3, h.loopRegs, h.pieceA, h.finArgs,
    h.pieceC, h.tail, h.exit⟩

/-- What the kernel checks of a hash function's own code (`core H`), the
same for every implementation of its compression function: the taint checks
of the pieces between calls, that no instruction loads MXCSR or writes
`rsp`, and how deeply calls nest. -/
structure CoreOK (C : Hash) : Prop where
  pbk : Pbk.Checks C
  iter : VG.Proof.Pbkdf2.X86_64.Checks C.P C.D
  hinit : HmacInit.Checks C
  hfin : HmacFin.Checks C
  pbkMx : C.pbkdf2.allInstrs (fun i => !loadsMxcsr i) = true
  pbkSp : C.pbkdf2.allInstrs (fun i => !isa.writesSp i) = true
  hinitMx : C.hmacInit.allInstrs (fun i => !loadsMxcsr i) = true
  hinitSp : C.hmacInit.allInstrs (fun i => !isa.writesSp i) = true
  hinitNs : C.hmacInit.allInstrs (fun i => !Taint.clobbers i .rsp) = true
  hinitD : C.hmacInit.depth ≤ 2
  hfinMx : C.hmacFin.allInstrs (fun i => !loadsMxcsr i) = true
  hfinSp : C.hmacFin.allInstrs (fun i => !isa.writesSp i) = true
  hfinNs : C.hmacFin.allInstrs (fun i => !Taint.clobbers i .rsp) = true
  hfinD : C.hmacFin.depth ≤ 2
  /-- The stack HMAC's functions use, without that of their callees. -/
  hinitXD : C.hmacInit.x86_64Depth ≤ 16
  hfinXD : C.hmacFin.x86_64Depth ≤ 16
  /-- The stack `pbkdf2` uses, without that of its callees' callees. -/
  pbkXD : C.pbkdf2.x86_64Depth ≤ 24
  iterMx : C.iterate.allInstrs (fun i => !loadsMxcsr i) = true
  iterSp : C.iterate.allInstrs (fun i => !isa.writesSp i) = true
  iterNs : C.iterate.allInstrs (fun i => !Taint.clobbers i .rsp) = true
  iterD : C.iterate.depth ≤ 2
  updMx : C.updC.allInstrs (fun i => !loadsMxcsr i) = true
  updNs : C.updC.allInstrs (fun i => !Taint.clobbers i .rsp) = true
  updD : C.updC.depth ≤ 1
  finMx : C.finC.allInstrs (fun i => !loadsMxcsr i) = true
  finNs : C.finC.allInstrs (fun i => !Taint.clobbers i .rsp) = true
  finD : C.finC.depth ≤ 1
  /-- HMAC's buffers fit in the working space. -/
  fitI : C.stream.buf ≤ 8 * C.W
  fitF : C.stream.buf + C.stream.F ≤ 8 * C.W

/-- What the kernel checks of `compBoth`, the code of HMAC's `init` that
compresses the blocks of its two states: its instructions, and that it is
one level of calls using no stack. -/
structure BothFacts (H : Hash) : Prop where
  bMx : H.compBoth.allInstrs (fun i => !loadsMxcsr i) = true
  bSp : H.compBoth.allInstrs (fun i => !isa.writesSp i) = true
  bNs : H.compBoth.allInstrs (fun i => !Taint.clobbers i .rsp) = true
  bD : H.compBoth.depth = 1
  bXD : H.compBoth.x86_64Depth = 8

/-- `compBoth` as the compression function twice (`compTwice`), from the
checks of the compression function. -/
theorem BothFacts.twice {H : Hash}
    (h : H.compBoth = Impl.Pbkdf2.Md.X86_64.compTwice H.P.N H.compN H.compC)
    (cMx : H.compC.allInstrs (fun i => !loadsMxcsr i) = true)
    (cSp : H.compC.allInstrs (fun i => !isa.writesSp i) = true)
    (cNs : H.compC.allInstrs (fun i => !Taint.clobbers i .rsp) = true)
    (cD : H.compC.depth = 0) (cXD : H.compC.x86_64Depth = 0) : BothFacts H where
  bMx := by
    rw [h]
    simp only [Impl.Pbkdf2.Md.X86_64.compTwice, Impl.Pbkdf2.Md.X86_64.outerArgs, Impl.MdStream.X86_64.compressAt,
      Impl.MdStream.X86_64.compressWith, Code.allInstrs, cMx, Bool.and_true, Bool.true_and]
    rfl
  bSp := by
    rw [h]
    simp only [Impl.Pbkdf2.Md.X86_64.compTwice, Impl.Pbkdf2.Md.X86_64.outerArgs, Impl.MdStream.X86_64.compressAt,
      Impl.MdStream.X86_64.compressWith, Code.allInstrs, cSp, Bool.and_true, Bool.true_and]
    rfl
  bNs := by
    rw [h]
    simp only [Impl.Pbkdf2.Md.X86_64.compTwice, Impl.Pbkdf2.Md.X86_64.outerArgs, Impl.MdStream.X86_64.compressAt,
      Impl.MdStream.X86_64.compressWith, Code.allInstrs, cNs, Bool.and_true, Bool.true_and]
    rfl
  bD := by
    rw [h]
    simp only [Impl.Pbkdf2.Md.X86_64.compTwice, Impl.MdStream.X86_64.compressAt,
      Impl.MdStream.X86_64.compressWith, Code.depth, cD]
    rfl
  bXD := by
    rw [h]
    simp only [Impl.Pbkdf2.Md.X86_64.compTwice, Impl.MdStream.X86_64.compressAt,
      Impl.MdStream.X86_64.compressWith, Code.x86_64Depth, cXD]
    rfl

/-- `compBoth` as one call of a function that compresses two blocks at once
(`compPair`), from the checks of that function. -/
theorem BothFacts.pair {H : Hash} {name : String} {code : Prog isa}
    (h : H.compBoth = Impl.Pbkdf2.Md.X86_64.compPair H.P.N name code)
    (pMx : code.allInstrs (fun i => !loadsMxcsr i) = true)
    (pSp : code.allInstrs (fun i => !isa.writesSp i) = true)
    (pNs : code.allInstrs (fun i => !Taint.clobbers i .rsp) = true)
    (pD : code.depth = 0) (pXD : code.x86_64Depth = 0) : BothFacts H where
  bMx := by
    rw [h]
    simp only [Impl.Pbkdf2.Md.X86_64.compPair, Impl.Pbkdf2.Md.X86_64.pairArgs, Code.allInstrs, pMx, Bool.and_true]
    rfl
  bSp := by
    rw [h]
    simp only [Impl.Pbkdf2.Md.X86_64.compPair, Impl.Pbkdf2.Md.X86_64.pairArgs, Code.allInstrs, pSp, Bool.and_true]
    rfl
  bNs := by
    rw [h]
    simp only [Impl.Pbkdf2.Md.X86_64.compPair, Impl.Pbkdf2.Md.X86_64.pairArgs, Code.allInstrs, pNs, Bool.and_true]
    rfl
  bD := by
    rw [h]
    simp only [Impl.Pbkdf2.Md.X86_64.compPair, Impl.Pbkdf2.Md.X86_64.pairArgs, Code.depth, pD]
    rfl
  bXD := by
    rw [h]
    simp only [Impl.Pbkdf2.Md.X86_64.compPair, Impl.Pbkdf2.Md.X86_64.pairArgs, Code.x86_64Depth, pXD]
    rfl

/-- What the kernel checks of the functions a hash function's code calls:
its compression function and its streaming `init`. -/
structure Callees (H : Hash) : Prop where
  cMx : H.compC.allInstrs (fun i => !loadsMxcsr i) = true
  cSp : H.compC.allInstrs (fun i => !isa.writesSp i) = true
  cNs : H.compC.allInstrs (fun i => !Taint.clobbers i .rsp) = true
  cD : H.compC.depth = 0
  iMx : H.initC.allInstrs (fun i => !loadsMxcsr i) = true
  iSp : H.initC.allInstrs (fun i => !isa.writesSp i) = true
  iNs : H.initC.allInstrs (fun i => !Taint.clobbers i .rsp) = true
  iD : H.initC.depth = 0
  /-- Neither uses any stack. -/
  cXD : H.compC.x86_64Depth = 0
  iXD : H.initC.x86_64Depth = 0
  /-- The same of `compBoth`, and what `init` needs of it. -/
  b : BothFacts H

/-- `Callees` of a hash function whose `compBoth` is its compression
function twice. -/
theorem Callees.ofTwice {H : Hash}
    (h : H.compBoth = Impl.Pbkdf2.Md.X86_64.compTwice H.P.N H.compN H.compC)
    (cMx : H.compC.allInstrs (fun i => !loadsMxcsr i) = true)
    (cSp : H.compC.allInstrs (fun i => !isa.writesSp i) = true)
    (cNs : H.compC.allInstrs (fun i => !Taint.clobbers i .rsp) = true)
    (cD : H.compC.depth = 0)
    (iMx : H.initC.allInstrs (fun i => !loadsMxcsr i) = true)
    (iSp : H.initC.allInstrs (fun i => !isa.writesSp i) = true)
    (iNs : H.initC.allInstrs (fun i => !Taint.clobbers i .rsp) = true)
    (iD : H.initC.depth = 0)
    (cXD : H.compC.x86_64Depth = 0) (iXD : H.initC.x86_64Depth = 0) : Callees H :=
  ⟨cMx, cSp, cNs, cD, iMx, iSp, iNs, iD, cXD, iXD, .twice h cMx cSp cNs cD cXD⟩

namespace Callees

variable {H : Hash} (K : Callees H) (C : CoreOK (core H))
include K C

theorem updMx : H.updC.allInstrs (fun i => !loadsMxcsr i) = true := core_updC K.cMx C.updMx
theorem finMx : H.finC.allInstrs (fun i => !loadsMxcsr i) = true := core_finC K.cMx C.finMx
theorem updSp : NoSp H.updC := nosp_of (core_updC K.cNs C.updNs)
theorem finSp : NoSp H.finC := nosp_of (core_finC K.cNs C.finNs)
theorem updD : H.updC.depth ≤ 1 := core_updC_depth K.cD C.updD
theorem finD : H.finC.depth ≤ 1 := core_finC_depth K.cD C.finD
theorem hmacInitXD : H.hmacInit.x86_64Depth ≤ 16 := core_hmacInit_xdepth K.iXD K.b.bXD C.hinitXD
theorem hmacFinXD : H.hmacFin.x86_64Depth ≤ 16 := core_hmacFin_xdepth K.cXD C.hfinXD
theorem pbkdf2XD : H.pbkdf2.x86_64Depth ≤ 24 := core_pbkdf2_xdepth K.cXD K.iXD K.b.bXD C.pbkXD

end Callees

/-- What the proofs need of `H.withWs so W`, the hash function's code made
with `so` bytes of working space for the compression function and `W` words
for our functions: `H`'s, but for what depends on them, the taint checks of
the streaming code (`Taints`) and of HMAC's and PBKDF2's (`CoreOK`), and the
compression function verified with that much working space. -/
def HashOK.withWs {H : Hash} (hH : HashOK H) (so W : Nat) (hso : so % 8 = 0 ∧ so + 48 ≤ 8 * 256)
    (taints : MdStream.X86_64.Taints { H.P with so := so })
    (comp : MdStream.X86_64.CalleeOk (P := { H.P with so := so }) hH.md H.compC)
    (fits : so + 48 + H.P.N + H.P.B ≤ 8 * W) (hW : W ≤ 256)
    (hb : H.compBoth = Impl.Pbkdf2.Md.X86_64.compTwice H.P.N H.compN H.compC) (K : Callees H)
    (C : CoreOK (core (H.withWs so W))) :
    HashOK (H.withWs so W) :=
  have K' : Callees (H.withWs so W) :=
    ⟨K.cMx, K.cSp, K.cNs, K.cD, K.iMx, K.iSp, K.iNs, K.iD, K.cXD, K.iXD,
      ⟨K.b.bMx, K.b.bSp, K.b.bNs, K.b.bD, K.b.bXD⟩⟩
  {
  md := hH.md
  dims := ⟨hH.dims.B, hH.dims.N, hH.dims.L, show so ≤ 2048 by omega_using [hso]⟩
  shape := ⟨hH.shape.len, hH.shape.lenV, hH.shape.out⟩
  taints := taints
  comp := comp
  both := .inl hb
  reloc := hH.reloc
  lenOk := hH.lenOk
  SH := hH.SH
  iv := hH.iv
  repr := hH.repr
  hash := hH.hash
  hB := hH.hB
  hS := hH.hS
  hD := hH.hD
  hD0 := hH.hD0
  hDN := hH.hDN
  hD4 := hH.hD4
  hN4 := hH.hN4
  hDL := hH.hDL
  hL4 := hH.hL4
  hNL := hH.hNL
  hPad := hH.hPad
  hso := hso
  fits := fits
  hW := hW
  init := hH.init
  initDepth := hH.initDepth
  initSp := hH.initSp
  updMx := Callees.updMx K' C
  finMx := Callees.finMx K' C
  updSp := Callees.updSp K' C
  finSp := Callees.finSp K' C
  updDepth := Callees.updD K' C
  finDepth := Callees.finD K' C }

/-- `Callees` of `H.withWs so W`: those of `H`, whose compression function and
streaming `init` it calls. -/
theorem Callees.withWs {H : Hash} (K : Callees H) (so W : Nat) : Callees (H.withWs so W) :=
  ⟨K.cMx, K.cSp, K.cNs, K.cD, K.iMx, K.iSp, K.iNs, K.iD, K.cXD, K.iXD,
    ⟨K.b.bMx, K.b.bSp, K.b.bNs, K.b.bD, K.b.bXD⟩⟩

/-! ## The functions, verified -/

/-- A state satisfying `pbkdf2`'s precondition, with `8 sc` bytes of scratch
space: an empty password, salt and output, and `c = 1`; the stack arguments
(`out_len` and `scratch`) are zero, so `scratch` is at address 0. -/
def pbkSat (sc : Nat) : State where
  gpr r := match r with
    | .rdi => 0x10000 | .rdx => 0x20000 | .r8 => 1 | .r9 => 0x30000
    | .rsp => 0x90000
    | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x10000, 0⟩, ⟨0x20000, 0⟩, ⟨0x90008, 16⟩]
  wr := [⟨0x30000, 0⟩, ⟨0, sc * 8⟩]

/-- A state satisfying the precondition of `pbkdf2` with its working space on
the stack: `pbkSat` without the working space, and with `out_len` its only
stack argument. -/
def pbkFrameSat : State :=
  { pbkSat 0 with rd := [⟨0x10000, 0⟩, ⟨0x20000, 0⟩, ⟨0x90008, 8⟩], wr := [⟨0x30000, 0⟩] }

section
variable {H : Hash} (hH : HashOK H) (C : CoreOK (core H)) (K : Callees H)
include hH C K

theorem hmacInit_ok (hsat : ∃ s, (Proof.Hmac.initScratchContract hH.SH H.W X86_64.abi 16).pre s) :
    Verified X86_64.target H.hmacInit (initG hH.SH H.W) :=
  HmacInit.verified hH (HmacInit.bothOk hH (HmacInit.Checks.of_core C.hinit)) (HmacInit.Checks.of_core C.hinit) C.fitI
    (core_hmacInit K.iMx K.b.bMx C.hinitMx)
    (initImp _ _ hsat).sat_left

theorem hmacFin_ok (hsat : ∃ s, (Proof.Hmac.finalizeScratchContract hH.SH H.W X86_64.abi 16).pre s) :
    Verified X86_64.target H.hmacFin (finG hH.SH H.W) :=
  HmacFin.verified hH (HmacFin.Checks.of_core C.hfin) C.fitF (core_hmacFin K.cMx C.hfinMx)
    (finImp _ _ hsat).sat_left

omit K in
theorem iterate_ok (hsat : ∃ s, (Proof.Pbkdf2.iterateContract hH.SH H.W X86_64.abi 8).pre s)
    (hmx : H.compC.allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified X86_64.target H.iterate (iterK hH.SH H.W) :=
  VG.Proof.Pbkdf2.X86_64.verified hH.iterOk C.iter hH.comp (core_iterate hmx C.iterMx) (iterImp _ _ hsat).sat_left

/-- HMAC's `init`, verified against the shared contract. -/
theorem hmacInit_verified (hsat : ∃ s, (Proof.Hmac.initScratchContract hH.SH H.W X86_64.abi 16).pre s) :
    Verified X86_64.target H.hmacInit (Proof.Hmac.initScratchContract hH.SH H.W X86_64.abi 16) :=
  (hmacInit_ok hH C K hsat).of_implies (initImp _ _ hsat)

/-- HMAC's `init`, verified against the shared contract with `sc` words of
working space: any that hold what it uses (`Stream.buf` bytes). -/
theorem hmacInit_verifiedW {sc : Nat} (hfit : H.stream.buf ≤ 8 * sc)
    (hsat : ∃ s, (Proof.Hmac.initScratchContract hH.SH sc X86_64.abi 16).pre s) :
    Verified X86_64.target H.hmacInit (Proof.Hmac.initScratchContract hH.SH sc X86_64.abi 16) :=
  (HmacInit.verified hH (HmacInit.bothOk hH (HmacInit.Checks.of_core C.hinit)) (HmacInit.Checks.of_core C.hinit)
    hfit (core_hmacInit K.iMx K.b.bMx C.hinitMx) (initImp _ _ hsat).sat_left).of_implies (initImp _ _ hsat)

/-- HMAC's `finalize`, verified against the shared contract. -/
theorem hmacFin_verified (hsat : ∃ s, (Proof.Hmac.finalizeScratchContract hH.SH H.W X86_64.abi 16).pre s) :
    Verified X86_64.target H.hmacFin (Proof.Hmac.finalizeScratchContract hH.SH H.W X86_64.abi 16) :=
  (hmacFin_ok hH C K hsat).of_implies (finImp _ _ hsat)

/-- `iterate`, verified against the shared contract. -/
theorem iterate_verified (hsat : ∃ s, (Proof.Pbkdf2.iterateContract hH.SH H.W X86_64.abi 8).pre s) :
    Verified X86_64.target H.iterate (Proof.Pbkdf2.iterateContract hH.SH H.W X86_64.abi 8) :=
  (iterate_ok hH C hsat K.cMx).of_implies (iterImp _ _ hsat)

/-- `pbkdf2`, verified against the contract its proof is written with. -/
theorem pbkdf2_ok
    (hsI : ∃ s, (Proof.Hmac.initScratchContract hH.SH H.W X86_64.abi 16).pre s)
    (hsF : ∃ s, (Proof.Hmac.finalizeScratchContract hH.SH H.W X86_64.abi 16).pre s)
    (hsT : ∃ s, (Proof.Pbkdf2.iterateContract hH.SH H.W X86_64.abi 8).pre s)
    (hsat : ∃ s, (pbkG hH.SH (H.W + H.S)).pre s) :
    Verified X86_64.target H.pbkdf2 (pbkG hH.SH (H.W + H.S)) :=
  Pbk.verified hH hH.psizes (Pbk.Checks.of_core C.pbk)
    (hmacInit_ok hH C K hsI) (nosp_of (core_hmacInit K.iNs K.b.bNs C.hinitNs))
    (core_hmacInit_depth K.iD K.b.bD C.hinitD)
    (hmacFin_ok hH C K hsF) (nosp_of (core_hmacFin K.cNs C.hfinNs)) (core_hmacFin_depth K.cD C.hfinD)
    (iterate_ok hH C hsT K.cMx) (nosp_of (core_iterate K.cNs C.iterNs)) (core_iterate_depth K.cD C.iterD)
    (core_pbkdf2 K.cMx K.iMx K.b.bMx C.pbkMx) hsat

/-- `pbkdf2`, verified against the shared contract. -/
theorem pbkdf2_verified
    (hsI : ∃ s, (Proof.Hmac.initScratchContract hH.SH H.W X86_64.abi 16).pre s)
    (hsF : ∃ s, (Proof.Hmac.finalizeScratchContract hH.SH H.W X86_64.abi 16).pre s)
    (hsT : ∃ s, (Proof.Pbkdf2.iterateContract hH.SH H.W X86_64.abi 8).pre s)
    (hsat : ∃ s, (Proof.Pbkdf2.pbkdf2ScratchContract hH.SH (H.W + H.S) X86_64.abi 24).pre s) :
    Verified X86_64.target H.pbkdf2 (Proof.Pbkdf2.pbkdf2ScratchContract hH.SH (H.W + H.S) X86_64.abi 24) :=
  (Pbk.verified hH hH.psizes (Pbk.Checks.of_core C.pbk)
    (hmacInit_ok hH C K hsI) (nosp_of (core_hmacInit K.iNs K.b.bNs C.hinitNs))
    (core_hmacInit_depth K.iD K.b.bD C.hinitD)
    (hmacFin_ok hH C K hsF) (nosp_of (core_hmacFin K.cNs C.hfinNs)) (core_hmacFin_depth K.cD C.hfinD)
    (iterate_ok hH C hsT K.cMx) (nosp_of (core_iterate K.cNs C.iterNs)) (core_iterate_depth K.cD C.iterD)
    (core_pbkdf2 K.cMx K.iMx K.b.bMx C.pbkMx) (pbkImp _ _ hsat).sat_left).of_implies (pbkImp _ _ hsat)

omit hH in
theorem hmacInit_sp : H.hmacInit.all (fun i => !isa.writesSp i) = true :=
  Code.all_of_allInstrs (core_hmacInit K.iSp K.b.bSp C.hinitSp)

omit hH in
theorem hmacFin_sp : H.hmacFin.all (fun i => !isa.writesSp i) = true :=
  Code.all_of_allInstrs (core_hmacFin K.cSp C.hfinSp)

omit hH in
theorem iterate_sp : H.iterate.all (fun i => !isa.writesSp i) = true :=
  Code.all_of_allInstrs (core_iterate K.cSp C.iterSp)

omit hH in
theorem pbkdf2_sp : H.pbkdf2.all (fun i => !isa.writesSp i) = true :=
  Code.all_of_allInstrs (core_pbkdf2 K.cSp K.iSp K.b.bSp C.pbkSp)

end

end VG.Proof.Pbkdf2.Md.X86_64
