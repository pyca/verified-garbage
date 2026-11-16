module
public import VerifiedGarbage.Impl.StackScratch.X86_64
public import VerifiedGarbage.Proof.Framework.X86_64.Depth
public import VerifiedGarbage.Proof.Blowfish.Scratch
public import VerifiedGarbage.Proof.Blowfish.X86_64.KeyP
public import VerifiedGarbage.Proof.Blowfish.KeyTable
import VerifiedGarbage.Proof.Blowfish.X86_64.Block
public import VerifiedGarbage.Proof.Blowfish.X86_64.Round
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Blowfish.X86_64.Ecb
public import VerifiedGarbage.Proof.Blowfish.X86_64.ConstantTime
import VerifiedGarbage.Proof.Framework.X86_64.Abi
public import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Blowfish.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
public import VerifiedGarbage.Impl.Blowfish.X86_64

/-! ### `Blowfish.X86_64.KeyVerified`, which only this module used -/

section

/-! ### `Blowfish.X86_64.KeyMain`, which only this module used -/

section

/-! ### `Blowfish.X86_64.KeyEnc`, which only this module used -/

section

/-! ### `Blowfish.X86_64.KeyStore`, which only this module used -/

section

/-!
# Key expansion: an encryption's output into the schedule

The output's halves go to the working space at `rcx` (`scratchOut_run`),
from there to `r11` and back into the halves (`take_run`), and to the
P-array as words (`store32_idx_run`) or to the S-boxes' planes a byte at a
time (`storeEntry_run`).
-/

@[expose] public section

namespace VG.Proof.Blowfish.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Blowfish.X86_64 VG.Spec.Blowfish VG.Proof.Blowfish

theorem scratchOut_run {t : State} {B : Addr} (hB : t.gpr .rcx = B) (hw : InRegions t.wr B 32) :
    runBlock isa outWords t = some { t with mem :=
      (t.mem.writeW (B + BitVec.ofNat 64 0) (t.xmm xR)).writeW (B + BitVec.ofNat 64 16) (t.xmm xL) } := by
  let t₁ : State := { t with mem := t.mem.writeW (B + BitVec.ofNat 64 0) (t.xmm xR) }
  obtain e0 : t.ea (mem .rcx 0) = B + BitVec.ofNat 64 0 := by rw [ea_mem, hB]
  obtain e16 : t₁.ea (mem .rcx 16) = B + BitVec.ofNat 64 16 := by rw [ea_mem]; exact congrArg (· + _) hB
  obtain h₁ : exec (.movdquStore (mem .rcx 0) xR) t = some t₁ := by
    rw [exec_movdquStore (by rw [e0]; exact inRegions_off hw (by omega_using [])), e0]
  let M := (t.mem.writeW (B + BitVec.ofNat 64 0) (t.xmm xR)).writeW (B + BitVec.ofNat 64 16) (t.xmm xL)
  obtain h₂ : exec (.movdquStore (mem .rcx 16) xL) t₁ = some { t with mem := M } := by
    rw [exec_movdquStore (by rw [e16]; exact inRegions_off hw (by omega_using [])), e16]
  rw [outWords, runBlock_cons, h₁, runStep_some, runBlock_cons, h₂, runStep_some, runBlock_nil]

/-- The word at `rcx + o` into `r11` and the low doubleword of `d`. -/
theorem take_run {t : State} {B : Addr} (hB : t.gpr .rcx = B) {o : Nat}
    (hr : InRegions (t.rd ++ t.wr) (B + BitVec.ofNat 64 o) 4) (d : XReg) :
    ∃ t', runBlock isa [.mov32 .r11 (.mem (mem .rcx o)), .xop (.movq d .r11)] t = some t' ∧
      t'.gpr .r11 = (t.mem.readW (B + BitVec.ofNat 64 o) 32).setWidth 64 ∧
      dword (t'.xmm d) 0 = t.mem.readW (B + BitVec.ofNat 64 o) 32 ∧
      (∀ d', d' ≠ d → t'.xmm d' = t.xmm d') ∧ (∀ g, g ≠ .r11 → t'.gpr g = t.gpr g) ∧ Upd t t' := by
  obtain e : t.ea (mem .rcx o) = B + BitVec.ofNat 64 o := by rw [ea_mem, hB]
  let t₁ := t.setReg32 .r11 (t.mem.readW (B + BitVec.ofNat 64 o) 32)
  obtain g₁ : t₁.gpr .r11 = (t.mem.readW (B + BitVec.ofNat 64 o) 32).setWidth 64 := by
    simp only [t₁, State.setReg32, gpr_setReg_self]
  refine ⟨(XOp.movq d .r11).exec t₁, ?_, ?_, ?_, fun d' h => ?_, fun g h => ?_, ?_⟩
  · rw [runBlock_cons, exec_mov32_mem (by rw [e]; exact hr), e, runStep_some, runBlock_cons, exec_xop, runStep_some,
      runBlock_nil]
  · simp only [XOp.exec, gpr_setXmm]; exact g₁
  · simp only [XOp.exec, xmm_setXmm_self]; exact dword_movq _ _ _ g₁
  · simp only [XOp.exec, xmm_setXmm_of_ne _ _ h, t₁, State.setReg32, xmm_setReg]
  · simp only [XOp.exec, gpr_setXmm, t₁, State.setReg32, gpr_setReg_of_ne _ _ h]
  · unfold Upd; simp only [XOp.exec, t₁, State.setReg32, State.setXmm, State.setReg]

/-- `r11`'s low doubleword at `rdx + rdi + o`. -/
theorem store32_idx_run {t : State} {S : Addr} {d o : Nat} (hS : t.gpr .rdx = S) (hd : t.gpr .rdi = BitVec.ofNat 64 d)
    (hw : InRegions t.wr (S + BitVec.ofNat 64 (o + d)) 4) :
    runBlock isa [.store32 { base := .rdx, index := some .rdi, disp := Int.ofNat o } .r11] t =
      some { t with mem := t.mem.writeW (S + BitVec.ofNat 64 (o + d)) ((t.gpr .r11).setWidth 32) } := by
  obtain e := ea_idx t .rdx .rdi S d o hS hd
  rw [runBlock_cons, exec_store32 (by rw [e]; exact hw), e, runStep_some, runBlock_nil]

theorem exec_store8 {s : State} {m : MemOp} {r : Reg} (h : InRegions s.wr (s.ea m) 1) :
    exec (.store8 m r) s = some { s with mem := s.mem.writeW (s.ea m) ((s.gpr r).setWidth 8) } := by
  simp only [exec, State.store8, h, ite_true]

theorem writeW8 (m : Mem) (a : Addr) (v : BitVec 8) : m.writeW a v = m.write a 1 v := by
  simp only [Mem.writeW, BitVec.setWidth_eq]

theorem shr_setWidth8 (x : BitVec 32) (k : Nat) : ((x >>> k).setWidth 64).setWidth 8 = x.extractLsb' k 8 := by
  rw [BitVec.setWidth_setWidth_of_le _ (by decide), shr_byte]

/-- The bytes of `r11`'s low doubleword into the four planes of the entry at
`rdx + rdi + e`. -/
theorem storeEntry_run {t : State} {S : Addr} {d e : Nat} (hS : t.gpr .rdx = S) (hd : t.gpr .rdi = BitVec.ofNat 64 d)
    (hw : ∀ b < 4, InRegions t.wr (S + BitVec.ofNat 64 (256 * b + e + d)) 1) :
    ∃ t', runBlock isa (storeEntry e) t = some t' ∧
      t'.mem = (((t.mem.write (S + BitVec.ofNat 64 (e + d)) 1 (((t.gpr .r11).setWidth 32).extractLsb' 0 8)).write
        (S + BitVec.ofNat 64 (256 + e + d)) 1 (((t.gpr .r11).setWidth 32).extractLsb' 8 8)).write
        (S + BitVec.ofNat 64 (512 + e + d)) 1 (((t.gpr .r11).setWidth 32).extractLsb' 16 8)).write
        (S + BitVec.ofNat 64 (768 + e + d)) 1 (((t.gpr .r11).setWidth 32).extractLsb' 24 8) ∧
      (∀ g, g ≠ .r11 → t'.gpr g = t.gpr g) ∧ t'.xmm = t.xmm ∧ UpdM t t' := by
  let w := (t.gpr .r11).setWidth 32
  obtain ea : ∀ (u : State) (o : Nat), u.gpr .rdx = S → u.gpr .rdi = BitVec.ofNat 64 d →
      u.ea { base := .rdx, index := some .rdi, disp := Int.ofNat o } = S + BitVec.ofNat 64 (o + d) :=
    fun u o h1 h2 => ea_idx u .rdx .rdi S d o h1 h2
  let t₁ : State := { t with mem := t.mem.writeW (S + BitVec.ofNat 64 (e + d)) ((t.gpr .r11).setWidth 8) }
  obtain ⟨t₂, e₂, r₂, g₂, xx₂, u₂⟩ := shift32_run t₁ .shr .r11 8 (by decide) (by decide)
  let t₃ : State := { t₂ with mem := t₂.mem.writeW (S + BitVec.ofNat 64 (256 + e + d)) ((t₂.gpr .r11).setWidth 8) }
  obtain ⟨t₄, e₄, r₄, g₄, xx₄, u₄⟩ := shift32_run t₃ .shr .r11 8 (by decide) (by decide)
  let t₅ : State := { t₄ with mem := t₄.mem.writeW (S + BitVec.ofNat 64 (512 + e + d)) ((t₄.gpr .r11).setWidth 8) }
  obtain ⟨t₆, e₆, r₆, g₆, xx₆, u₆⟩ := shift32_run t₅ .shr .r11 8 (by decide) (by decide)
  let t₇ : State := { t₆ with mem := t₆.mem.writeW (S + BitVec.ofNat 64 (768 + e + d)) ((t₆.gpr .r11).setWidth 8) }
  obtain G : ∀ g, g ≠ .r11 → t₆.gpr g = t.gpr g := fun g h => by
    rw [g₆ _ h, show t₅.gpr = t₄.gpr from rfl, g₄ _ h, show t₃.gpr = t₂.gpr from rfl, g₂ _ h]
  obtain G₂ : ∀ g, g ≠ .r11 → t₂.gpr g = t.gpr g := fun g h => by rw [g₂ _ h]
  obtain G₄ : ∀ g, g ≠ .r11 → t₄.gpr g = t.gpr g := fun g h => by
    rw [g₄ _ h, show t₃.gpr = t₂.gpr from rfl, G₂ _ h]
  obtain W : ∀ u : State, UpdM t u → ∀ b < 4, InRegions u.wr (S + BitVec.ofNat 64 (256 * b + e + d)) 1 :=
    fun u hu b hb => by rw [hu]; exact hw b hb
  obtain U₂ : UpdM t t₂ := UpdM.trans (UpdM.of_upd u₂) (UpdM.store _)
  obtain U₄ : UpdM t t₄ := UpdM.trans (UpdM.of_upd u₄) (UpdM.trans (UpdM.store _) U₂)
  obtain U₆ : UpdM t t₆ := UpdM.trans (UpdM.of_upd u₆) (UpdM.trans (UpdM.store _) U₄)
  obtain v₂ : t₂.gpr .r11 = (w >>> 8).setWidth 64 := by rw [r₂]; simp only [reduceCtorEq, ↓reduceIte]; rfl
  obtain v₄ : t₄.gpr .r11 = (w >>> 16).setWidth 64 := by
    rw [r₄, show t₃.gpr = t₂.gpr from rfl, v₂]
    simp only [reduceCtorEq, ↓reduceIte, setWidth_setWidth_32, ← BitVec.shiftRight_add, Nat.reduceAdd]
  obtain v₆ : t₆.gpr .r11 = (w >>> 24).setWidth 64 := by
    rw [r₆, show t₅.gpr = t₄.gpr from rfl, v₄]
    simp only [reduceCtorEq, ↓reduceIte, setWidth_setWidth_32, ← BitVec.shiftRight_add, Nat.reduceAdd]
  obtain w1 : InRegions t₂.wr (S + BitVec.ofNat 64 (256 + e + d)) 1 := by
    have := W t₂ U₂ 1 (by decide); simpa using this
  obtain w2 : InRegions t₄.wr (S + BitVec.ofNat 64 (512 + e + d)) 1 := by
    have := W t₄ U₄ 2 (by decide); simpa using this
  obtain w3 : InRegions t₆.wr (S + BitVec.ofNat 64 (768 + e + d)) 1 := by
    have := W t₆ U₆ 3 (by decide); simpa using this
  refine ⟨t₇, ?_, ?_, fun g h => G g h, by show t₆.xmm = t.xmm; rw [xx₆]; show t₄.xmm = t.xmm; rw [xx₄]; exact xx₂,
    UpdM.trans (UpdM.store _) U₆⟩
  · rw [storeEntry, runBlock_cons,
      exec_store8 (by rw [ea t _ hS hd]; have := hw 0 (by decide); simpa using this), ea t _ hS hd, runStep_some,
      runBlock_cons, e₂, runStep_some, runBlock_cons,
      exec_store8 (by rw [ea t₂ _ ((G₂ _ (by decide)).trans hS) ((G₂ _ (by decide)).trans hd)]; exact w1),
      ea t₂ _ ((G₂ _ (by decide)).trans hS) ((G₂ _ (by decide)).trans hd), runStep_some,
      runBlock_cons, e₄, runStep_some, runBlock_cons,
      exec_store8 (by rw [ea t₄ _ ((G₄ _ (by decide)).trans hS) ((G₄ _ (by decide)).trans hd)]; exact w2),
      ea t₄ _ ((G₄ _ (by decide)).trans hS) ((G₄ _ (by decide)).trans hd), runStep_some,
      runBlock_cons, e₆, runStep_some, runBlock_cons,
      exec_store8 (by rw [ea t₆ _ ((G _ (by decide)).trans hS) ((G _ (by decide)).trans hd)]; exact w3),
      ea t₆ _ ((G _ (by decide)).trans hS) ((G _ (by decide)).trans hd), runStep_some, runBlock_nil]
  · show t₆.mem.writeW _ ((t₆.gpr .r11).setWidth 8) = _
    rw [v₆, shr_setWidth8, writeW8, show t₆.mem = t₅.mem by rw [u₆]]
    show (t₄.mem.writeW _ ((t₄.gpr .r11).setWidth 8)).write _ _ _ = _
    rw [v₄, shr_setWidth8, writeW8, show t₄.mem = t₃.mem by rw [u₄]]
    show ((t₂.mem.writeW _ ((t₂.gpr .r11).setWidth 8)).write _ _ _).write _ _ _ = _
    rw [v₂, shr_setWidth8, writeW8, show t₂.mem = t₁.mem by rw [u₂]]
    show (((t.mem.writeW _ ((t.gpr .r11).setWidth 8)).write _ _ _).write _ _ _).write _ _ _ = _
    rw [writeW8, show (t.gpr .r11).setWidth 8 = w.extractLsb' 0 8 by
      rw [show w = w >>> 0 by simp, ← shr_byte]; simp only [w, BitVec.ushiftRight_zero]
      rw [BitVec.setWidth_setWidth_of_le _ (by decide)]]

end VG.Proof.Blowfish.X86_64

end

end


/-!
# Key expansion: the 521 encryptions

Each encryption runs ECB's rounds under the schedule as written so far,
and its output replaces the next two entries: the P-array's, as words
(`encryptP_run`), then the S-boxes', a byte per plane (`encryptS_run`).
-/

@[expose] public section

namespace VG.Proof.Blowfish.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Blowfish.X86_64 VG.Spec.Blowfish VG.Proof.Blowfish

/-- What the encryptions need, of the state they start in. -/
structure EncEnv (S B : Addr) (s₀ : State) : Prop where
  rdx : s₀.gpr .rdx = S
  rcx : s₀.gpr .rcx = B
  wrS : SchedW S s₀
  wrB : InRegions s₀.wr B 32
  sep : (⟨S, 4168⟩ : Region).Disjoint ⟨B, 32⟩
  fitS : S.toNat + 4168 ≤ 2 ^ 64
  fitB : B.toNat + 32 ≤ 2 ^ 64
  ones : s₀.xmm onesReg = wordsOf 1
  sixteen : s₀.xmm sixteenReg = wordsOf 16
  low : s₀.xmm lowReg = wordsOf 0xFF

/-- The registers an encryption and its stores write. -/
abbrev EncRegs (g : Reg) : Prop :=
  g ≠ .rax ∧ g ≠ .rsi ∧ g ≠ .rdi ∧ g ≠ .r8 ∧ g ≠ .r9 ∧ g ≠ .r10 ∧ g ≠ .r11

/-- After `j` encryptions. -/
structure EncInv (key : List Byte) (S B : Addr) (s₀ : State) (j : Nat) (u : State) : Prop where
  le : j ≤ 521
  sched : scheduleAt u.mem S = (ksIter key j).1
  xl : dword (u.xmm xL) 0 = (ksIter key j).2.1
  xr : dword (u.xmm xR) 0 = (ksIter key j).2.2
  gpr : ∀ g, EncRegs g → u.gpr g = s₀.gpr g
  xmm : ∀ d, d ∉ cXRegs → u.xmm d = s₀.xmm d
  frame : Frame [⟨S, 4168⟩, ⟨B, 32⟩] s₀.mem u.mem
  eq : UpdM s₀ u

theorem EncInv.rdx {key : List Byte} {S B : Addr} {s₀ : State} (E : EncEnv S B s₀) {j : Nat} {u : State}
    (I : EncInv key S B s₀ j u) : u.gpr .rdx = S := (I.gpr _ (by decide)).trans E.rdx

theorem EncInv.rcx {key : List Byte} {S B : Addr} {s₀ : State} (E : EncEnv S B s₀) {j : Nat} {u : State}
    (I : EncInv key S B s₀ j u) : u.gpr .rcx = B := (I.gpr _ (by decide)).trans E.rcx

theorem EncInv.wrS {key : List Byte} {S B : Addr} {s₀ : State} (E : EncEnv S B s₀) {j : Nat} {u : State}
    (I : EncInv key S B s₀ j u) : SchedW S u := fun off n h => by rw [I.eq]; exact E.wrS off n h

theorem EncInv.wrB {key : List Byte} {S B : Addr} {s₀ : State} (E : EncEnv S B s₀) {j : Nat} {u : State}
    (I : EncInv key S B s₀ j u) : InRegions u.wr B 32 := by rw [I.eq]; exact E.wrB

/-- The encryption of the last output. -/
theorem enc_cipher {key : List Byte} {S B : Addr} {s₀ : State} (E : EncEnv S B s₀) {j : Nat} {u : State}
    (I : EncInv key S B s₀ j u) :
    WP isa (cipher .rdx true) u (fun u' =>
      dword (u'.xmm xR) 0 = (encryptWords (ksIter key j).1 (ksIter key j).2.1 (ksIter key j).2.2).1 ∧
      dword (u'.xmm xL) 0 = (encryptWords (ksIter key j).1 (ksIter key j).2.1 (ksIter key j).2.2).2 ∧
      COnly u u') := by
  obtain W := I.wrS E
  obtain CE : CipherEnv .rdx S u :=
    ⟨⟨I.rdx E, by decide, by decide, by decide, fun off h => inRegions_append_right (W off 16 (by omega_arith)),
      by rw [I.xmm _ (by decide), E.ones], by rw [I.xmm _ (by decide), E.sixteen],
      by rw [I.xmm _ (by decide), E.low]⟩, by decide, by decide,
      fun i hi => inRegions_append_right (W _ 4 (by omega_arith))⟩
  refine WP.mono (cipher_run CE true) fun u' ⟨h1, h2, O⟩ => ⟨?_, ?_, O⟩
  · rw [h1, I.sched, I.xl, I.xr]; rfl
  · rw [h2, I.sched, I.xl, I.xr]; rfl

theorem ksIter_step (key : List Byte) {j : Nat} (hj : j < 521) :
    ksIter key (j + 1) =
      (((ksIter key j).1.set (2 * j) (encryptWords (ksIter key j).1 (ksIter key j).2.1 (ksIter key j).2.2).1
          (by omega_arith)).set (2 * j + 1)
          (encryptWords (ksIter key j).1 (ksIter key j).2.1 (ksIter key j).2.2).2 (by omega_arith),
        (encryptWords (ksIter key j).1 (ksIter key j).2.1 (ksIter key j).2.2).1,
        (encryptWords (ksIter key j).1 (ksIter key j).2.1 (ksIter key j).2.2).2) := by
  rw [ksIter_succ, ksStep, set!_eq_set _ (by omega_arith), set!_eq_set _ (by omega_arith)]

/-- The scratch writes leave the schedule as it was. -/
theorem scheduleAt_scratch {S B : Addr} (sep : (⟨S, 4168⟩ : Region).Disjoint ⟨B, 32⟩)
    (m : Mem) (x y : BitVec 128) :
    scheduleAt ((m.writeW (B + BitVec.ofNat 64 0) x).writeW (B + BitVec.ofNat 64 16) y) S = scheduleAt m S :=
  scheduleAt_eq_of_frame S (rs := [⟨B, 32⟩])
    (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains_base B (by omega_arith) (by omega_arith))).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base B (by omega_arith) (by omega_arith)))
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact sep)

theorem readW_scratch0 {B : Addr} (m : Mem) (x y : BitVec 128) :
    ((m.writeW (B + BitVec.ofNat 64 0) x).writeW (B + BitVec.ofNat 64 16) y).readW (B + BitVec.ofNat 64 0) 32 =
      dword x 0 := by
  rw [Mem.readW_writeW_sep (Offset.sep B (by omega_arith) (by omega_arith) (by omega_arith)) (by decide), readW_writeW128_0]

theorem readW_scratch16 {B : Addr} (m : Mem) (x y : BitVec 128) :
    ((m.writeW (B + BitVec.ofNat 64 0) x).writeW (B + BitVec.ofNat 64 16) y).readW (B + BitVec.ofNat 64 16) 32 =
      dword y 0 := readW_writeW128_0 _ _ _

/-- `r11`'s low doubleword at `rdx + rdi + o`. -/
abbrev pStore (o : Nat) : Instr := .store32 { base := .rdx, index := some .rdi, disp := Int.ofNat o } .r11

theorem withMem_run {b : List Instr} {t : State} {M : Mem} (h : runBlock isa b t = some { t with mem := M }) :
    ∃ t', runBlock isa b t = some t' ∧ t'.mem = M ∧ t'.gpr = t.gpr ∧ t'.xmm = t.xmm ∧ t'.rd = t.rd ∧
      t'.wr = t.wr ∧ UpdM t t' := ⟨_, h, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The working space's word at `B + o` apart from the schedule's at `S + e`. -/
theorem sep_scratch {S B : Addr} (sep : (⟨S, 4168⟩ : Region).Disjoint ⟨B, 32⟩) {o e : Nat} (ho : o + 4 ≤ 32)
    (he : e + 4 ≤ 4168) : Mem.Sep (B + BitVec.ofNat 64 o) (32 / 8) (S + BitVec.ofNat 64 e) (32 / 8) :=
  sep_of_disjoint ((sep.symm.sub_left (Offset.sub_base B ho)).sub_right (Offset.sub_base S he))

/-- An encryption's output into P-array entries `2 j` and `2 j + 1`. -/
theorem encP_step {key : List Byte} {S B : Addr} {s₀ : State} (E : EncEnv S B s₀) {j : Nat} (hj : j < 9)
    {u : State} (I : EncInv key S B s₀ j u) (hrdi : u.gpr .rdi = BitVec.ofNat 64 (8 * j))
    (hrsi : u.gpr .rsi = BitVec.ofNat 64 (9 - j)) :
    WP isa (.seq (cipher .rdx true) (.block (storeP ++ ([.alu .add .rdi (.imm 8), .alu .sub .rsi (.imm 1)] : List Instr)))) u
      (fun u' => EncInv key S B s₀ (j + 1) u' ∧ u'.gpr .rdi = BitVec.ofNat 64 (8 * (j + 1)) ∧
        u'.gpr .rsi = BitVec.ofNat 64 (9 - (j + 1)) ∧ u'.zf = some (BitVec.ofNat 64 (9 - (j + 1)) == 0)) := by
  have fitS := E.fitS
  apply WP.seq
  refine WP.mono (enc_cipher E I) fun u₁ ⟨h1, h2, O⟩ => ?_
  let out := encryptWords (ksIter key j).1 (ksIter key j).2.1 (ksIter key j).2.2
  obtain wr₁ : u₁.wr = u.wr := by rw [O.upd]
  have g₁ : ∀ g, g ≠ .rax → g ≠ .r8 → g ≠ .r9 → g ≠ .r10 → g ≠ .r11 → u₁.gpr g = u.gpr g := O.gpr
  obtain rcx₁ : u₁.gpr .rcx = B := (g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans (I.rcx E)
  obtain rdx₁ : u₁.gpr .rdx = S := (g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans (I.rdx E)
  obtain rdi₁ : u₁.gpr .rdi = BitVec.ofNat 64 (8 * j) :=
    (g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hrdi
  obtain W : SchedW S u₁ := fun off n h => by rw [wr₁]; exact I.wrS E off n h
  -- the halves to the working space
  let M₂ := (u₁.mem.writeW (B + BitVec.ofNat 64 0) (u₁.xmm xR)).writeW (B + BitVec.ofNat 64 16) (u₁.xmm xL)
  obtain ⟨u₂, r₂, m₂, gp₂, x₂, rd₂, wr₂, up₂⟩ := withMem_run (scratchOut_run rcx₁ (by rw [wr₁]; exact I.wrB E))
  obtain rB : ∀ o, o + 4 ≤ 32 → InRegions (u₂.rd ++ u₂.wr) (B + BitVec.ofNat 64 o) 4 := fun o ho => by
    rw [rd₂, wr₂, wr₁, show u₁.rd = u.rd by rw [O.upd]]
    exact inRegions_append_right (inRegions_off (I.wrB E) ho)
  obtain ⟨u₃, r₃, a₃, x₃, k₃, g₃, up₃⟩ := take_run (t := u₂) (by rw [gp₂]; exact rcx₁) (rB 0 (by omega_arith)) xL
  obtain A₃ : (u₃.gpr .r11).setWidth 32 = out.1 := by
    rw [a₃, setWidth_setWidth_32, m₂, readW_scratch0, h1]
  obtain m₃ : u₃.mem = M₂ := by rw [up₃]; exact m₂
  obtain wr₃ : u₃.wr = u.wr := by rw [up₃]; rw [wr₂]; exact wr₁
  obtain rd₃ : u₃.rd = u.rd := by rw [up₃]; rw [rd₂]; rw [O.upd]
  obtain G₃ : ∀ g, g ≠ .r11 → u₃.gpr g = u₁.gpr g := fun g h => by rw [g₃ _ h, gp₂]
  let M₄ := M₂.writeW (S + BitVec.ofNat 64 (pOff + 8 * j)) ((u₃.gpr .r11).setWidth 32)
  obtain ⟨u₄, r₄, m₄, gp₄, x₄, rd₄, wr₄, up₄⟩ := withMem_run (b := [pStore pOff]) (M := M₄)
    (by rw [store32_idx_run (S := S) (d := 8 * j) (o := pOff) ((G₃ _ (by decide)).trans rdx₁)
      ((G₃ _ (by decide)).trans rdi₁) (by rw [wr₃]; exact I.wrS E _ _ (by simp only [pOff]; omega_arith)), m₃])
  obtain rB₄ : InRegions (u₄.rd ++ u₄.wr) (B + BitVec.ofNat 64 16) 4 := by
    rw [rd₄, wr₄, rd₃, wr₃]; exact inRegions_append_right (inRegions_off (I.wrB E) (by omega_arith))
  obtain ⟨u₅, r₅, a₅, x₅, k₅, g₅, up₅⟩ := take_run (t := u₄) (o := 16)
    ((congrFun gp₄ .rcx).trans ((G₃ _ (by decide)).trans rcx₁)) rB₄ xR
  obtain B₅ : (u₅.gpr .r11).setWidth 32 = out.2 := by
    rw [a₅, setWidth_setWidth_32, m₄]
    rw [Mem.readW_writeW_sep (sep_scratch (o := 16) (e := pOff + 8 * j) E.sep (by omega_arith) (by simp only [pOff]; omega_arith)) (by decide), readW_scratch16, h2]
  obtain m₅ : u₅.mem = M₄ := by rw [up₅]; exact m₄
  obtain wr₅ : u₅.wr = u.wr := by rw [up₅]; rw [wr₄]; exact wr₃
  obtain G₅ : ∀ g, g ≠ .r11 → u₅.gpr g = u₁.gpr g := fun g h => by rw [g₅ _ h, gp₄]; exact G₃ _ h
  let M₆ := M₄.writeW (S + BitVec.ofNat 64 (pOff + 4 + 8 * j)) ((u₅.gpr .r11).setWidth 32)
  obtain ⟨u₆, r₆, m₆, gp₆, x₆, rd₆, wr₆, up₆⟩ := withMem_run (b := [pStore (pOff + 4)]) (M := M₆)
    (by rw [store32_idx_run (S := S) (d := 8 * j) (o := pOff + 4) ((G₅ _ (by decide)).trans rdx₁)
      ((G₅ _ (by decide)).trans rdi₁) (by rw [wr₅]; exact I.wrS E _ _ (by simp only [pOff]; omega_arith)), m₅])
  obtain ⟨u₇, e₇, a₇, k₇, x₇, up₇⟩ := add_imm_run u₆ .rdi 8
  obtain ⟨u₈, e₈, a₈, z₈, k₈, x₈, up₈⟩ := sub_imm_run u₇ .rsi 1
  obtain mem₈ : u₈.mem = M₆ := by rw [up₈, up₇]; exact m₆
  obtain xmm₈ : u₈.xmm = u₅.xmm := by rw [x₈, x₇, x₆]
  obtain G₈ : ∀ g, g ≠ .rdi → g ≠ .rsi → g ≠ .r11 → u₈.gpr g = u₁.gpr g := fun g h1 h2 h3 => by
    rw [k₈ _ h2, k₇ _ h1, gp₆]; exact G₅ g h3
  refine WP.of_runBlock ⟨u₈, ?_, ⟨by omega_arith, ?_, ?_, ?_, fun g hg => ?_, fun d hd => ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [storeP, List.append_assoc]
    refine cat_run r₂ ?_
    rw [show ([.mov32 .r11 (.mem (mem .rcx 0)), .xop (.movq xL .r11), pStore pOff,
        .mov32 .r11 (.mem (mem .rcx 16)), .xop (.movq xR .r11), pStore (pOff + 4)] ++
        [.alu .add .rdi (.imm 8), .alu .sub .rsi (.imm 1)] : List Instr) =
        ([.mov32 .r11 (.mem (mem .rcx 0)), .xop (.movq xL .r11)] : List Instr) ++ ([pStore pOff] ++
        (([.mov32 .r11 (.mem (mem .rcx 16)), .xop (.movq xR .r11)] : List Instr) ++ ([pStore (pOff + 4)] ++
        ([.alu .add .rdi (.imm 8), .alu .sub .rsi (.imm 1)] : List Instr)))) from rfl]
    refine cat_run r₃ (cat_run r₄ (cat_run r₅ (cat_run r₆ ?_)))
    rw [runBlock_cons, e₇, runStep_some, runBlock_cons, e₈, runStep_some, runBlock_nil]
  · rw [mem₈, ksIter_step key (by omega_arith)]
    rw [show M₆ = M₄.writeW _ ((u₅.gpr .r11).setWidth 32) from rfl, B₅, show pOff + 4 + 8 * j = 4096 + 4 * (2 * j + 1) by simp only [pOff]; omega_arith,
      scheduleAt_writeW_P _ _ (by omega_arith)]
    rw [show M₄ = M₂.writeW _ ((u₃.gpr .r11).setWidth 32) from rfl, A₃, show pOff + 8 * j = 4096 + 4 * (2 * j) by simp only [pOff]; omega_arith, scheduleAt_writeW_P _ _ (by omega_arith),
      scheduleAt_scratch E.sep, show u₁.mem = u.mem by rw [O.upd], I.sched]
  · rw [xmm₈, k₅ _ (by decide), x₄, x₃, m₂, readW_scratch0, h1, ksIter_step key (by omega_arith)]
  · have b := B₅
    rw [a₅, setWidth_setWidth_32] at b
    rw [xmm₈, x₅, b, ksIter_step key (by omega_arith)]
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hg
    rw [G₈ g h3 h2 h7, g₁ g h1 h4 h5 h6 h7]; exact I.gpr g ⟨h1, h2, h3, h4, h5, h6, h7⟩
  · have n0 : d ≠ xL := fun e => hd (by rw [e]; decide)
    obtain n1 : d ≠ xR := fun e => hd (by rw [e]; decide)
    rw [xmm₈, k₅ _ n1, x₄, k₃ _ n0, x₂, O.xmm d hd, I.xmm d hd]
  · rw [mem₈]
    obtain hS : ∀ e, e + 4 ≤ 4168 → (⟨S, 4168⟩ : Region).Contains (S + BitVec.ofNat 64 e) (32 / 8) :=
      fun e he => Offset.contains_base S he (by omega_arith)
    have mS : (⟨S, 4168⟩ : Region) ∈ [⟨S, 4168⟩, ⟨B, 32⟩] := List.mem_cons_self
    obtain mB : (⟨B, 32⟩ : Region) ∈ [⟨S, 4168⟩, ⟨B, 32⟩] := List.mem_cons_of_mem _ List.mem_cons_self
    refine ((((I.frame.trans ?_).writeW mB _ (Offset.contains_base B (by omega_arith) (by omega_arith))).writeW mB _
      (Offset.contains_base B (by omega_arith) (by omega_arith))).writeW mS _ (hS _ (by simp only [pOff]; omega_arith))).writeW mS _
      (hS _ (by simp only [pOff]; omega_arith))
    rw [show u₁.mem = u.mem by rw [O.upd]]; exact Frame.refl _ _
  · exact UpdM.trans (UpdM.of_upd up₈) (UpdM.trans (UpdM.of_upd up₇) (UpdM.trans up₆
      (UpdM.trans (UpdM.of_upd up₅) (UpdM.trans up₄ (UpdM.trans (UpdM.of_upd up₃)
        (UpdM.trans up₂ (UpdM.trans (UpdM.of_upd O.upd) I.eq)))))))
  · rw [k₈ _ (by decide), a₇, gp₆, G₅ _ (by decide), rdi₁]
    apply BitVec.eq_of_toNat_eq; simp; omega_arith
  · rw [a₈, k₇ _ (by decide), gp₆, G₅ _ (by decide),
      g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide), hrsi]
    apply BitVec.eq_of_toNat_eq; simp; omega_arith
  · rw [z₈, k₇ _ (by decide), gp₆, G₅ _ (by decide),
      g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide), hrsi,
      show BitVec.ofNat 64 (9 - j) - BitVec.signExtend 64 (1 : BitVec 32) = BitVec.ofNat 64 (9 - (j + 1)) from by
        apply BitVec.eq_of_toNat_eq; simp; omega_arith]

/-- The offset of S-box entry `sDone j`'s first plane. -/
def sOff (j : Nat) : Nat := 1024 * (sDone j / 256) + sDone j % 256

theorem sOff_entry {j : Nat} (h9 : 9 ≤ j) (hj : j < 521) {b k : Nat} (hk : k < 2) :
    256 * b + k + sOff j = entryOff (2 * j + k) b := by
  rw [← entryOff_sbox h9 hj k hk, sOff]; omega_arith

theorem sOff_lt {j : Nat} (h9 : 9 ≤ j) (hj : j < 521) : sOff j ≤ 3326 := by
  unfold sOff sDone; omega_arith

theorem sOff_succ {j : Nat} (h9 : 9 ≤ j) :
    sOff (j + 1) = if (sOff j + 2) % 256 = 0 then sOff j + 2 + 768 else sOff j + 2 := by
  unfold sOff sDone; split <;> omega_arith

theorem and_255 {x : Nat} (h : x < 2 ^ 64) : (BitVec.ofNat 64 x &&& BitVec.ofNat 64 255).toNat = x % 256 := by
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h,
    show (255 % 2 ^ 64) = 2 ^ 8 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]

theorem test_imm_run (t : State) (d : Reg) (v : BitVec 32) :
    ∃ t', exec (.alu .test d (.imm v)) t = some t' ∧ t'.zf = some ((t.gpr d &&& v.signExtend 64) == 0) ∧
      t'.gpr = t.gpr ∧ t'.xmm = t.xmm ∧ Upd t t' :=
  ⟨_, rfl, rfl, rfl, rfl, by unfold Upd; simp only [arithFlags, State.setFlags]⟩

/-- `storeEntry_run` at the offsets of entry `i`. -/
theorem storeEntry_at {t : State} {S : Addr} {d e i : Nat} (hS : t.gpr .rdx = S) (hd : t.gpr .rdi = BitVec.ofNat 64 d)
    (hoff : ∀ b < 4, 256 * b + e + d = entryOff i b)
    (hw : ∀ b < 4, InRegions t.wr (S + BitVec.ofNat 64 (entryOff i b)) 1) :
    ∃ t', runBlock isa (storeEntry e) t = some t' ∧
      t'.mem = (((t.mem.write (S + BitVec.ofNat 64 (entryOff i 0)) 1 (((t.gpr .r11).setWidth 32).extractLsb' 0 8)).write
        (S + BitVec.ofNat 64 (entryOff i 1)) 1 (((t.gpr .r11).setWidth 32).extractLsb' 8 8)).write
        (S + BitVec.ofNat 64 (entryOff i 2)) 1 (((t.gpr .r11).setWidth 32).extractLsb' 16 8)).write
        (S + BitVec.ofNat 64 (entryOff i 3)) 1 (((t.gpr .r11).setWidth 32).extractLsb' 24 8) ∧
      (∀ g, g ≠ .r11 → t'.gpr g = t.gpr g) ∧ t'.xmm = t.xmm ∧ UpdM t t' := by
  obtain ⟨t', r, m, g, x, u⟩ := storeEntry_run (e := e) hS hd fun b hb => by rw [hoff b hb]; exact hw b hb
  refine ⟨t', r, ?_, g, x, u⟩
  obtain h0 := hoff 0 (by decide)
  obtain h1 := hoff 1 (by decide)
  obtain h2 := hoff 2 (by decide)
  obtain h3 := hoff 3 (by decide)
  rw [m, show e + d = entryOff i 0 by omega_arith, show 256 + e + d = entryOff i 1 by omega_arith,
    show 512 + e + d = entryOff i 2 by omega_arith, show 768 + e + d = entryOff i 3 by omega_arith]

/-- The four byte writes of an entry stay in the schedule. -/
theorem frame_bytes {rs : List Region} {m m' : Mem} (h : Frame rs m m') {S : Addr} (hS : (⟨S, 4168⟩ : Region) ∈ rs)
    {i : Nat} (hi : i < 1042) (w : Word) :
    Frame rs m ((((m'.write (S + BitVec.ofNat 64 (entryOff i 0)) 1 (w.extractLsb' 0 8)).write
        (S + BitVec.ofNat 64 (entryOff i 1)) 1 (w.extractLsb' 8 8)).write
        (S + BitVec.ofNat 64 (entryOff i 2)) 1 (w.extractLsb' 16 8)).write
        (S + BitVec.ofNat 64 (entryOff i 3)) 1 (w.extractLsb' 24 8)) :=
  have c : ∀ b < 4, (⟨S, 4168⟩ : Region).Contains (S + BitVec.ofNat 64 (entryOff i b)) 1 := fun b hb =>
    Offset.contains_base S (by have := entryOff_lt hi hb; omega_arith) (by have := entryOff_lt hi hb; omega_arith)
  (((h.write hS _ (c 0 (by decide))).write hS _ (c 1 (by decide))).write hS _ (c 2 (by decide))).write hS _
    (c 3 (by decide))

/-- An encryption's output into S-box entries `2 j` and `2 j + 1` (`sDone j`
and the next of the S-boxes). -/
theorem encS_step {key : List Byte} {S B : Addr} {s₀ : State} (E : EncEnv S B s₀) {j : Nat} (h9 : 9 ≤ j)
    (hj : j < 521) {u : State} (I : EncInv key S B s₀ j u) (hrdi : u.gpr .rdi = BitVec.ofNat 64 (sOff j))
    (hrsi : u.gpr .rsi = BitVec.ofNat 64 (521 - j)) :
    WP isa (.seq (cipher .rdx true)
        (.seq (.block (storeS ++ ([.alu .add .rdi (.imm 2), .alu .test .rdi (.imm 255)] : List Instr)))
          (.seq (.ite .e (.block [.alu .add .rdi (.imm 768)]) (.block [])) (.block [.alu .sub .rsi (.imm 1)])))) u
      (fun u' => EncInv key S B s₀ (j + 1) u' ∧ u'.gpr .rdi = BitVec.ofNat 64 (sOff (j + 1)) ∧
        u'.gpr .rsi = BitVec.ofNat 64 (521 - (j + 1)) ∧ u'.zf = some (BitVec.ofNat 64 (521 - (j + 1)) == 0)) := by
  have fitS := E.fitS
  obtain so := sOff_lt h9 hj
  apply WP.seq
  refine WP.mono (enc_cipher E I) fun u₁ ⟨h1, h2, O⟩ => ?_
  let out := encryptWords (ksIter key j).1 (ksIter key j).2.1 (ksIter key j).2.2
  obtain wr₁ : u₁.wr = u.wr := by rw [O.upd]
  obtain rd₁ : u₁.rd = u.rd := by rw [O.upd]
  have g₁ : ∀ g, g ≠ .rax → g ≠ .r8 → g ≠ .r9 → g ≠ .r10 → g ≠ .r11 → u₁.gpr g = u.gpr g := O.gpr
  obtain rcx₁ : u₁.gpr .rcx = B := (g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans (I.rcx E)
  obtain rdx₁ : u₁.gpr .rdx = S := (g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans (I.rdx E)
  obtain rdi₁ : u₁.gpr .rdi = BitVec.ofNat 64 (sOff j) :=
    (g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hrdi
  obtain hw : ∀ (t : State), t.wr = u.wr → ∀ k < 2, ∀ b < 4,
      InRegions t.wr (S + BitVec.ofNat 64 (entryOff (2 * j + k) b)) 1 := fun t ht k hk b hb => by
    rw [ht]; exact I.wrS E _ _ (by have := entryOff_lt (i := 2 * j + k) (by omega_arith) hb; omega_arith)
  obtain hoff : ∀ k < 2, ∀ b < 4, 256 * b + k + sOff j = entryOff (2 * j + k) b :=
    fun k hk b _ => sOff_entry h9 hj hk
  -- the halves to the working space
  let M₂ := (u₁.mem.writeW (B + BitVec.ofNat 64 0) (u₁.xmm xR)).writeW (B + BitVec.ofNat 64 16) (u₁.xmm xL)
  obtain ⟨u₂, r₂, m₂, gp₂, x₂, rd₂, wr₂, up₂⟩ := withMem_run (scratchOut_run rcx₁ (by rw [wr₁]; exact I.wrB E))
  obtain rB : ∀ o, o + 4 ≤ 32 → InRegions (u.rd ++ u.wr) (B + BitVec.ofNat 64 o) 4 := fun o ho =>
    inRegions_append_right (inRegions_off (I.wrB E) ho)
  obtain ⟨u₃, r₃, a₃, x₃, k₃, g₃, up₃⟩ := take_run (t := u₂) (B := B) (o := 0) (by rw [gp₂]; exact rcx₁)
    (by rw [rd₂, wr₂, wr₁, rd₁]; exact rB 0 (by omega_arith)) xL
  obtain A₃ : (u₃.gpr .r11).setWidth 32 = out.1 := by
    rw [a₃, setWidth_setWidth_32, m₂, readW_scratch0, h1]
  obtain m₃ : u₃.mem = M₂ := by rw [up₃]; exact m₂
  obtain wr₃ : u₃.wr = u.wr := by rw [up₃]; rw [wr₂]; exact wr₁
  obtain rd₃ : u₃.rd = u.rd := by rw [up₃]; rw [rd₂]; exact rd₁
  obtain G₃ : ∀ g, g ≠ .r11 → u₃.gpr g = u₁.gpr g := fun g h => by rw [g₃ _ h, gp₂]
  obtain ⟨u₄, r₄, m₄, G₄, x₄, up₄⟩ := storeEntry_at (e := 0) (i := 2 * j + 0) ((G₃ _ (by decide)).trans rdx₁)
    ((G₃ _ (by decide)).trans rdi₁) (fun b hb => hoff 0 (by decide) b hb) (hw u₃ wr₃ 0 (by decide))
  obtain wr₄ : u₄.wr = u.wr := by rw [up₄]; exact wr₃
  obtain rd₄ : u₄.rd = u.rd := by rw [up₄]; exact rd₃
  obtain f₄ : Frame [⟨S, 4168⟩] M₂ u₄.mem := by
    rw [m₄, m₃]; exact frame_bytes (Frame.refl _ _) (List.mem_singleton_self _) (by omega_arith) _
  obtain ⟨u₅, r₅, a₅, x₅, k₅, g₅, up₅⟩ := take_run (t := u₄) (o := 16)
    ((G₄ _ (by decide)).trans ((G₃ _ (by decide)).trans rcx₁)) (by rw [rd₄, wr₄]; exact rB 16 (by omega_arith)) xR
  obtain B₅ : (u₅.gpr .r11).setWidth 32 = out.2 := by
    rw [a₅, setWidth_setWidth_32,
      f₄.readW (r := ⟨B + BitVec.ofNat 64 16, 4⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (E.sep.symm.sub_left (Offset.sub_base B (by omega_arith)))) (by decide),
      readW_scratch16, h2]
  obtain wr₅ : u₅.wr = u.wr := by rw [up₅]; exact wr₄
  obtain G₅ : ∀ g, g ≠ .r11 → u₅.gpr g = u₁.gpr g := fun g h => by rw [g₅ _ h, G₄ _ h]; exact G₃ _ h
  obtain ⟨u₆, r₆, m₆, G₆, x₆, up₆⟩ := storeEntry_at (e := 1) (i := 2 * j + 1) ((G₅ _ (by decide)).trans rdx₁)
    ((G₅ _ (by decide)).trans rdi₁) (fun b hb => hoff 1 (by decide) b hb) (hw u₅ wr₅ 1 (by decide))
  obtain ⟨u₇, e₇, a₇, k₇, x₇, up₇⟩ := add_imm_run u₆ .rdi 2
  obtain ⟨u₈, e₈, z₈, gp₈, xx₈, up₈⟩ := test_imm_run u₇ .rdi 255
  obtain G₈ : ∀ g, g ≠ .rdi → g ≠ .r11 → u₈.gpr g = u₁.gpr g := fun g h1 h2 => by
    rw [gp₈, k₇ _ h1, G₆ _ h2]; exact G₅ _ h2
  obtain rdi₈ : u₈.gpr .rdi = BitVec.ofNat 64 (sOff j + 2) := by
    rw [gp₈, a₇, G₆ _ (by decide), G₅ _ (by decide), rdi₁]
    exact BitVec.eq_of_toNat_eq (by simp)
  obtain mem₈ : u₈.mem = u₆.mem := by rw [show u₈.mem = u₇.mem by rw [up₈]]; rw [up₇]
  obtain xmm₈ : u₈.xmm = u₅.xmm := by rw [xx₈, x₇, x₆]
  obtain m₅ : u₅.mem = u₄.mem := by rw [up₅]
  obtain U₈ : UpdM u u₈ := UpdM.trans (UpdM.of_upd up₈) (UpdM.trans (UpdM.of_upd up₇) (UpdM.trans up₆
      (UpdM.trans (UpdM.of_upd up₅) (UpdM.trans up₄ (UpdM.trans (UpdM.of_upd up₃)
        (UpdM.trans up₂ (UpdM.of_upd O.upd)))))))
  -- the invariant, but for `rdi` and `rsi`
  obtain I₈ : ∀ v : State, UpdM u₈ v → v.mem = u₈.mem → v.xmm = u₈.xmm →
      (∀ g, g ≠ .rdi → g ≠ .rsi → v.gpr g = u₈.gpr g) → EncInv key S B s₀ (j + 1) v := by
    intro v uv mv xv gv
    refine ⟨by omega_arith, ?_, ?_, ?_, fun g hg => ?_, fun d hd => ?_, ?_, uv.trans (U₈.trans I.eq)⟩
    · rw [mv, mem₈, m₆, scheduleAt_write_bytes _ _ (by omega_arith), B₅, m₅, m₄,
        scheduleAt_write_bytes _ _ (by omega_arith), A₃, m₃, scheduleAt_scratch E.sep,
        show u₁.mem = u.mem by rw [O.upd], I.sched, ksIter_step key (by omega_arith)]
      rfl
    · rw [xv, xmm₈, k₅ _ (by decide), x₄, x₃, m₂, readW_scratch0, h1, ksIter_step key (by omega_arith)]
    · have b := B₅
      rw [a₅, setWidth_setWidth_32] at b
      rw [xv, xmm₈, x₅, b, ksIter_step key (by omega_arith)]
    · obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hg
      rw [gv g h3 h2, G₈ g h3 h7, g₁ g h1 h4 h5 h6 h7]; exact I.gpr g ⟨h1, h2, h3, h4, h5, h6, h7⟩
    · have n0 : d ≠ xL := fun e => hd (by rw [e]; decide)
      obtain n1 : d ≠ xR := fun e => hd (by rw [e]; decide)
      rw [xv, xmm₈, k₅ _ n1, x₄, k₃ _ n0, x₂, O.xmm d hd, I.xmm d hd]
    · rw [mv, mem₈, m₆]
      have mS : (⟨S, 4168⟩ : Region) ∈ [⟨S, 4168⟩, ⟨B, 32⟩] := List.mem_cons_self
      obtain mB : (⟨B, 32⟩ : Region) ∈ [⟨S, 4168⟩, ⟨B, 32⟩] := List.mem_cons_of_mem _ List.mem_cons_self
      refine frame_bytes ?_ mS (by omega_arith) _
      rw [m₅, m₄, m₃]
      refine frame_bytes ?_ mS (by omega_arith) _
      refine ((I.frame.trans ?_).writeW mB _ (Offset.contains_base B (by omega_arith) (by omega_arith))).writeW mB _
        (Offset.contains_base B (by omega_arith) (by omega_arith))
      rw [show u₁.mem = u.mem by rw [O.upd]]; exact Frame.refl _ _
  obtain so' := sOff_succ h9 (j := j)
  apply WP.seq
  refine WP.of_runBlock ⟨u₈, ?_, ?_⟩
  · rw [storeS, List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc]
    refine cat_run r₂ (cat_run r₃ (cat_run r₄ (cat_run r₅ (cat_run r₆ ?_))))
    rw [runBlock_cons, e₇, runStep_some, runBlock_cons, e₈, runStep_some, runBlock_nil]
  obtain zf₈ : isa.eval .e u₈ = some ((sOff j + 2) % 256 == 0) := by
    show u₈.zf = _
    rw [z₈, show u₇.gpr .rdi = u₈.gpr .rdi by rw [gp₈], rdi₈,
      show BitVec.signExtend 64 (255 : BitVec 32) = BitVec.ofNat 64 255 from rfl]
    congr 1
    by_cases h : (sOff j + 2) % 256 = 0
    · rw [beq_iff_eq.mpr h]; apply beq_iff_eq.mpr; apply BitVec.eq_of_toNat_eq; rw [and_255 (by omega_arith), h]; rfl
    · rw [beq_eq_false_iff_ne.mpr h]; apply beq_eq_false_iff_ne.mpr; intro e
      have := congrArg BitVec.toNat e; rw [and_255 (by omega_arith)] at this; exact h this
  apply WP.seq
  -- the next S-box, after its last entry
  obtain fin : ∀ v : State, UpdM u₈ v → v.mem = u₈.mem → v.xmm = u₈.xmm →
      (∀ g, g ≠ .rdi → v.gpr g = u₈.gpr g) → v.gpr .rdi = BitVec.ofNat 64 (sOff (j + 1)) →
      WP isa (.block [.alu .sub .rsi (.imm 1)]) v (fun u' => EncInv key S B s₀ (j + 1) u' ∧
        u'.gpr .rdi = BitVec.ofNat 64 (sOff (j + 1)) ∧ u'.gpr .rsi = BitVec.ofNat 64 (521 - (j + 1)) ∧
        u'.zf = some (BitVec.ofNat 64 (521 - (j + 1)) == 0)) := by
    intro v uv mv xv gv rv
    obtain ⟨w, e, a, z, k, x, up⟩ := sub_imm_run v .rsi 1
    obtain rsi₈ : v.gpr .rsi = BitVec.ofNat 64 (521 - j) := by
      rw [gv _ (by decide), G₈ _ (by decide) (by decide),
        g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide), hrsi]
    obtain r : BitVec.ofNat 64 (521 - j) - BitVec.signExtend 64 (1 : BitVec 32) = BitVec.ofNat 64 (521 - (j + 1)) := by
      apply BitVec.eq_of_toNat_eq; simp; omega_arith
    refine WP.of_runBlock ⟨w, by rw [runBlock_cons, e, runStep_some, runBlock_nil],
      I₈ w ((UpdM.of_upd up).trans uv) (by rw [up]; exact mv) (by rw [x]; exact xv)
        (fun g h1 h2 => by rw [k _ h2]; exact gv g h1), by rw [k _ (by decide)]; exact rv,
      by rw [a, rsi₈, r], by rw [z, rsi₈, r]⟩
  apply WP.ite _ zf₈
  · intro h
    obtain h' : (sOff j + 2) % 256 = 0 := by simpa using h
    obtain ⟨v, e, a, k, x, up⟩ := add_imm_run u₈ .rdi 768
    refine WP.of_runBlock ⟨v, by rw [runBlock_cons, e, runStep_some, runBlock_nil],
      fin v (UpdM.of_upd up) (by rw [up]) x (fun g h1 => k g h1) ?_⟩
    rw [a, rdi₈, so', itT _ _ h']
    apply BitVec.eq_of_toNat_eq; simp
  · intro h
    obtain h' : ¬ (sOff j + 2) % 256 = 0 := by simpa using h
    refine WP.block_nil (fin u₈ (by unfold UpdM; rfl) rfl rfl (fun _ _ => rfl) ?_)
    rw [rdi₈, so', itF _ _ h']

end VG.Proof.Blowfish.X86_64

end

end


/-!
# The key expansion function

The initial schedule written, the P-array keyed, the constants set, and
the 521 encryptions run (`expandKey_correct`).
-/

@[expose] public section

namespace VG.Proof.Blowfish.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Blowfish.X86_64 VG.Spec.Blowfish VG.Proof.Blowfish

theorem EncInv.of_upd {key : List Byte} {S B : Addr} {s₀ : State} {j : Nat} {u v : State}
    (I : EncInv key S B s₀ j u) (hv : UpdM u v) (hm : v.mem = u.mem) (hx : v.xmm = u.xmm)
    (hg : ∀ g, EncRegs g → v.gpr g = u.gpr g) : EncInv key S B s₀ j v :=
  ⟨I.le, by rw [hm]; exact I.sched, by rw [hx]; exact I.xl, by rw [hx]; exact I.xr,
    fun g h => (hg g h).trans (I.gpr g h), fun d h => by rw [hx]; exact I.xmm d h, by rw [hm]; exact I.frame,
    hv.trans I.eq⟩

theorem setReg32_upd (t : State) (r : Reg) (v : BitVec 32) : UpdM t (t.setReg32 r v) := by
  unfold UpdM; simp only [State.setReg32, State.setReg]

/-- The nine encryptions replacing the P-array. -/
theorem encryptP_run {key : List Byte} {S B : Addr} {s₀ : State} (E : EncEnv S B s₀) {u : State}
    (I : EncInv key S B s₀ 0 u) : WP isa encryptP u (EncInv key S B s₀ 9) := by
  rw [encryptP]
  apply WP.seq
  let u₁ := (u.setReg32 .rdi 0).setReg32 .rsi 9
  refine WP.of_runBlock ⟨u₁, by
    rw [runBlock_cons, exec_mov32_imm, runStep_some, runBlock_cons, exec_mov32_imm, runStep_some, runBlock_nil], ?_⟩
  obtain I₁ : EncInv key S B s₀ 0 u₁ :=
    I.of_upd ((setReg32_upd _ _ _).trans (setReg32_upd _ _ _)) rfl rfl fun g ⟨_, h2, h3, _⟩ => by
      simp only [u₁, State.setReg32, gpr_setReg_of_ne _ _ h2, gpr_setReg_of_ne _ _ h3]
  obtain hd₁ : u₁.gpr .rdi = BitVec.ofNat 64 (8 * 0) := by
    simp only [u₁, State.setReg32, gpr_setReg_of_ne _ _ (show Reg.rdi ≠ Reg.rsi by decide), gpr_setReg_self]; rfl
  obtain hs₁ : u₁.gpr .rsi = BitVec.ofNat 64 (9 - 0) := by simp only [u₁, State.setReg32, gpr_setReg_self]; rfl
  refine WP.loop (M := isa) (fun m v => ∃ j, j < 9 ∧ m = 9 - j ∧ EncInv key S B s₀ j v ∧
      v.gpr .rdi = BitVec.ofNat 64 (8 * j) ∧ v.gpr .rsi = BitVec.ofNat 64 (9 - j)) ?_ 9 u₁
    ⟨0, by omega_using [], rfl, I₁, hd₁, hs₁⟩
  intro m v ⟨j, hj, hm, I, hd, hs⟩
  refine WP.mono (encP_step E hj I hd hs) fun v' ⟨I', d', s', z'⟩ => ?_
  obtain ev : isa.eval .ne v' = some (!(BitVec.ofNat 64 (9 - (j + 1)) == 0)) := by
    show v'.zf.map (!·) = _; rw [z']; rfl
  by_cases h : j + 1 = 9
  · left; exact ⟨by rw [ev, h]; rfl, h ▸ I'⟩
  · right
    obtain nz : BitVec.ofNat 64 (9 - (j + 1)) ≠ 0 := by
      intro h'; have := congrArg BitVec.toNat h'; simp at this; omega_using [hj, h, this]
    exact ⟨by rw [ev, show (BitVec.ofNat 64 (9 - (j + 1)) == 0) = false from beq_false_of_ne nz]; rfl,
      9 - (j + 1), by omega_using [hj, hm], j + 1, by omega_using [hj, h], rfl, I', d', s'⟩

/-- The other 512, replacing the S-boxes. -/
theorem encryptS_run {key : List Byte} {S B : Addr} {s₀ : State} (E : EncEnv S B s₀) {u : State}
    (I : EncInv key S B s₀ 9 u) : WP isa encryptS u (EncInv key S B s₀ 521) := by
  rw [encryptS]
  apply WP.seq
  let u₁ := (u.setReg32 .rdi 0).setReg32 .rsi 512
  refine WP.of_runBlock ⟨u₁, by
    rw [runBlock_cons, exec_mov32_imm, runStep_some, runBlock_cons, exec_mov32_imm, runStep_some, runBlock_nil], ?_⟩
  obtain I₁ : EncInv key S B s₀ 9 u₁ :=
    I.of_upd ((setReg32_upd _ _ _).trans (setReg32_upd _ _ _)) rfl rfl fun g ⟨_, h2, h3, _⟩ => by
      simp only [u₁, State.setReg32, gpr_setReg_of_ne _ _ h2, gpr_setReg_of_ne _ _ h3]
  obtain hd₁ : u₁.gpr .rdi = BitVec.ofNat 64 (sOff 9) := by
    simp only [u₁, State.setReg32, gpr_setReg_of_ne _ _ (show Reg.rdi ≠ Reg.rsi by decide), gpr_setReg_self]; rfl
  obtain hs₁ : u₁.gpr .rsi = BitVec.ofNat 64 (521 - 9) := by simp only [u₁, State.setReg32, gpr_setReg_self]; rfl
  refine WP.loop (M := isa) (fun m v => ∃ j, 9 ≤ j ∧ j < 521 ∧ m = 521 - j ∧ EncInv key S B s₀ j v ∧
      v.gpr .rdi = BitVec.ofNat 64 (sOff j) ∧ v.gpr .rsi = BitVec.ofNat 64 (521 - j)) ?_ 512 u₁
    ⟨9, by omega_using [], by omega_using [], rfl, I₁, hd₁, hs₁⟩
  intro m v ⟨j, h9, hj, hm, I, hd, hs⟩
  refine WP.mono (encS_step E h9 hj I hd hs) fun v' ⟨I', d', s', z'⟩ => ?_
  obtain ev : isa.eval .ne v' = some (!(BitVec.ofNat 64 (521 - (j + 1)) == 0)) := by
    show v'.zf.map (!·) = _; rw [z']; rfl
  by_cases h : j + 1 = 521
  · left; exact ⟨by rw [ev, h]; rfl, h ▸ I'⟩
  · right
    obtain nz : BitVec.ofNat 64 (521 - (j + 1)) ≠ 0 := by
      intro h'; have := congrArg BitVec.toNat h'; simp at this; omega_using [hj, h, this]
    exact ⟨by rw [ev, show (BitVec.ofNat 64 (521 - (j + 1)) == 0) = false from beq_false_of_ne nz]; rfl,
      521 - (j + 1), by omega_using [hj, hm], j + 1, by omega_using [h9], by omega_using [hj, h], rfl, I', d', s'⟩

/-- What key expansion may assume. -/
structure KeyPre (s : State) : Prop where
  valid : validKey (s.gpr .rsi).toNat
  rd : s.rd = [⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩]
  wr : s.wr = [⟨s.gpr .rdx, 4168⟩, ⟨s.gpr .rcx, 32⟩]
  keySch : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨s.gpr .rdx, 4168⟩
  schBuf : (⟨s.gpr .rdx, 4168⟩ : Region).Disjoint ⟨s.gpr .rcx, 32⟩
  fitK : (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64
  fitS : (s.gpr .rdx).toNat + 4168 ≤ 2 ^ 64
  fitB : (s.gpr .rcx).toNat + 32 ≤ 2 ^ 64

/-- What key expansion guarantees. -/
structure KeyPost (s s' : State) : Prop where
  sched : scheduleAt s'.mem (s.gpr .rdx) = expandKey (bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
  gpr : ∀ g, EncRegs g → s'.gpr g = s.gpr g
  frame : Frame [⟨s.gpr .rdx, 4168⟩, ⟨s.gpr .rcx, 32⟩] s.mem s'.mem

theorem pxor_self_run (t : State) (d : XReg) :
    ∃ t', runBlock isa [bin .pxor d d] t = some t' ∧ dword (t'.xmm d) 0 = 0 ∧
      (∀ d', d' ≠ d → t'.xmm d' = t.xmm d') ∧ t'.gpr = t.gpr ∧ Upd t t' := by
  refine ⟨(XOp.bin .pxor d d).exec t, by rw [bin, runBlock_cons, exec_xop, runStep_some, runBlock_nil], ?_,
    fun d' h => ?_, rfl, ?_⟩
  · simp only [XOp.exec, xmm_setXmm_self, XBinOp.eval, BitVec.xor_self]; rfl
  · simp only [XOp.exec, xmm_setXmm_of_ne _ _ h]
  · unfold Upd; simp only [XOp.exec, State.setXmm]

theorem expandKey_correct {s : State} (P : KeyPre s) :
    WP isa Impl.Blowfish.X86_64.expandKey s (KeyPost s) := by
  let K := s.gpr .rdi
  let L := (s.gpr .rsi).toNat
  let S := s.gpr .rdx
  let B := s.gpr .rcx
  have fitS := P.fitS
  have fitB := P.fitB
  have hL : 4 ≤ L ∧ L ≤ 56 := P.valid
  obtain hL64 : L < 2 ^ 64 := (s.gpr .rsi).isLt
  obtain mS : (⟨S, 4168⟩ : Region) ∈ s.wr := by rw [P.wr]; exact List.mem_cons_self
  rw [Impl.Blowfish.X86_64.expandKey]
  -- the initial schedule
  apply WP.seq
  obtain ⟨t₁, r₁, d₁, f₁, g₁, e₁⟩ := initSteps_run (S := S) (t := s) rfl (SchedW.of_mem mS) 521 (by omega_using [])
  refine WP.of_runBlock ⟨t₁, by rw [initSchedule_eq]; exact r₁, ?_⟩
  obtain rd₁ : t₁.rd = s.rd := by rw [e₁]
  obtain wr₁ : t₁.wr = s.wr := by rw [e₁]
  obtain hT : ∀ o < 4168, t₁.mem (S + BitVec.ofNat 64 o) = Impl.Blowfish.initByte o :=
    fun o ho => table_byte (fun i hi => by rw [initWords_getD hi]; exact d₁ i hi) ho
  obtain keyS : ∀ c < L, ¬ (⟨S, 4168⟩ : Region).Contains (K + BitVec.ofNat 64 c) 1 := fun c hc h =>
    P.keySch _ (Offset.contains_base K (by omega_using [hc]) (by omega_using [hc])) h
  obtain hB₁ : bytesAt t₁.mem K L = bytesAt s.mem K L := bytesAt_frame f₁ fun c hc r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact keyS c hc
  -- the keyed P-array
  apply WP.seq
  obtain KE : KeyPEnv S K L t₁ :=
    ⟨by omega_using [hL], hL64, fun c hc => by
        rw [rd₁, wr₁, P.rd]; exact ⟨_, List.mem_cons_self, Offset.contains_base K (by omega_using [hc]) (by omega_using [hc])⟩,
      by rw [g₁ _ (by decide)], by rw [g₁ _ (by decide)]; simp [L],
      by rw [g₁ _ (by decide)], SchedW.of_mem (by rw [wr₁]; exact mS), fitS, keyS⟩
  refine WP.mono (keyP_run KE) fun t₂ I₂ => ?_
  obtain hK : scheduleAt t₂.mem S = keyed (bytesAt s.mem K L) := by
    refine keyed_of_mem (fun o ho => ?_) (fun i hi => ?_)
    · rw [I₂.frame.bytes (R := ⟨S, 4096⟩) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.base_disjoint S (by omega_using []) (by omega_using [])) (by show 4096 ≤ 2 ^ 64; decide) ho]
      exact hT o (by omega_using [ho])
    · rw [I₂.done i hi, table_P hT hi, hB₁]
  -- the constants and the zero block
  apply WP.seq
  obtain ⟨t₃, r₃, o₃, x₃, l₃, k₃, g₃, up₃⟩ := constants_run t₂
  obtain ⟨t₄, r₄, z₄, k₄, g₄, up₄⟩ := pxor_self_run t₃ xL
  obtain ⟨t₅, r₅, z₅, k₅, g₅, up₅⟩ := pxor_self_run t₄ xR
  refine WP.of_runBlock ⟨t₅, cat_run r₃ (cat_run r₄ r₅), ?_⟩
  obtain U₅ : UpdM t₂ t₅ := UpdM.trans (UpdM.of_upd up₅) (UpdM.trans (UpdM.of_upd up₄) (UpdM.of_upd up₃))
  obtain m₅ : t₅.mem = t₂.mem := by
    rw [show t₅.mem = t₄.mem by rw [up₅], show t₄.mem = t₃.mem by rw [up₄], up₃]
  obtain G₅ : ∀ g, g ≠ .r11 → t₅.gpr g = t₂.gpr g := fun g h => by rw [g₅, g₄, g₃ _ h]
  obtain G₂ : ∀ g, g ≠ .rax → g ≠ .r8 → g ≠ .r10 → g ≠ .r11 → t₂.gpr g = s.gpr g := fun g h1 h2 h3 h4 => by
    rw [I₂.gpr g h1 h2 h3 h4, g₁ g h4]
  obtain EE : EncEnv S B t₅ := by
    refine ⟨by rw [G₅ _ (by decide), G₂ _ (by decide) (by decide) (by decide) (by decide)],
      by rw [G₅ _ (by decide), G₂ _ (by decide) (by decide) (by decide) (by decide)],
      SchedW.of_mem (by rw [U₅, I₂.eq, wr₁]; exact mS),
      by rw [U₅, I₂.eq, wr₁, P.wr]; exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Region.contains_self _ _⟩,
      P.schBuf, fitS, fitB, ?_, ?_, ?_⟩
    · rw [k₅ _ (by decide), k₄ _ (by decide), o₃]
    · rw [k₅ _ (by decide), k₄ _ (by decide), x₃]
    · rw [k₅ _ (by decide), k₄ _ (by decide), l₃]
  obtain I₅ : EncInv (bytesAt s.mem K L) S B t₅ 0 t₅ :=
    ⟨by omega_using [], by rw [m₅, hK]; rfl, by rw [k₅ _ (by decide), z₄]; rfl, by rw [z₅]; rfl,
      fun _ _ => rfl, fun _ _ => rfl, Frame.refl _ _, by unfold UpdM; rfl⟩
  -- the encryptions
  apply WP.seq
  refine WP.mono (encryptP_run EE I₅) fun t₆ I₆ => ?_
  refine WP.mono (encryptS_run EE I₆) fun t₇ I₇ => ?_
  refine ⟨by rw [I₇.sched, ← expandKey_eq], fun g hg => ?_, ?_⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hg
    rw [I₇.gpr g ⟨h1, h2, h3, h4, h5, h6, h7⟩, G₅ g h7, G₂ g h1 h4 h6 h7]
  · refine Frame.trans ?_ (I₇.frame.trans (Frame.refl _ _))
    rw [m₅]
    refine Frame.trans (f₁.mono fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self) ?_
    refine Frame.sub I₂.frame fun r hr => ⟨⟨S, 4168⟩, List.mem_cons_self, ?_⟩
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.sub_base S (by omega_using [])

end VG.Proof.Blowfish.X86_64

end

end


/-! # Key expansion meets its contract, with the working space as an argument -/

@[expose] public section

namespace VG.Proof.Blowfish.X86_64

open VG VG.X86_64 VG.Impl.Blowfish.X86_64 VG.Spec.Blowfish VG.Proof.Blowfish

/-- The key expansion contract as the code sees it. -/
def keyC : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
    let sch : Region := ⟨s.gpr .rdx, 4168⟩
    let buf : Region := ⟨s.gpr .rcx, 32⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [key] ∧ s.wr = [sch, buf] ∧ key.Disjoint sch ∧ key.Disjoint buf ∧ sch.Disjoint buf ∧
      ret.Disjoint sch ∧ ret.Disjoint buf ∧ validKey (s.gpr .rsi).toNat ∧
      (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + 4168 ≤ 2 ^ 64 ∧
      (s.gpr .rcx).toNat + 32 ≤ 2 ^ 64
  post s s' := scheduleAt s'.mem (s.gpr .rdx) = expandKey (bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
  pub := PublicRegs [.rdi, .rsi, .rdx, .rcx, .rsp]

def keySatState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 16 | .rdx => 0x2000 | .rcx => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 4168⟩, ⟨0x4000, 32⟩]

theorem expandKey_ok (s : State) (hs : keyC.pre s) :
    ∃ t s', Exec isa Impl.Blowfish.X86_64.expandKey s t s' ∧ abiPreserved s s' ∧ keyC.post s s' := by
  obtain ⟨rd, wr, kS, -, SB, rS, rB, valid, fK, fS, fB⟩ := hs
  obtain ⟨t, s', he, hp⟩ := expandKey_correct ⟨valid, rd, wr, kS, SB, fK, fS, fB⟩
  refine ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he ⟨fun r hr => ?_, ?_⟩, hp.sched⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact hp.gpr _ (by decide)
  · refine hp.frame.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) ?_ (by decide)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact rS
    · exact rB

theorem expandKey_verified :
    Verified target Impl.Blowfish.X86_64.expandKey (Proof.Blowfish.expandKeyScratchContract abi) := by
  refine Verified.of_correct (k := keyC) expandKey_ok (expandKey_constantTime _) ?_
  sig_implies [Proof.Blowfish.expandKeyScratchContract, Proof.Blowfish.expandKeyScratchSig, Spec.Blowfish.expandKeyPre,
    Spec.Blowfish.expandKeyPost, Spec.Blowfish.validKey, abi, argRegs, keyC, publicRegs_five] [keySatState]
    using keySatState

end VG.Proof.Blowfish.X86_64

end

end


/-!
# Blowfish on x86-64, with its working space on the stack

Key expansion and ECB run their code, proved with the working space as an
argument, in a frame that allocates it and zeroes the bytes the code uses
after the code (`Verified.stackScratchWiped`), since they hold the key
schedule's intermediate blocks and the data: 40 bytes for key expansion (32
of working space) and 264 for ECB (256, of which it uses 16), with 8 more to
keep `rsp` aligned. The code uses no other stack.
-/

@[expose] public section

namespace VG.Proof.Blowfish.X86_64

open VG VG.X86_64

/-- A state satisfying `vg_blowfish_expand_key`'s precondition: a 16-byte key
at `0x1000` and the schedule at `0x2000`. -/
def expandKeyFrameSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 16 | .rdx => 0x2000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 4168⟩]

theorem expandKeyFrameSat_pre : ∃ s, (Spec.Blowfish.expandKeyContract X86_64.abi 40).pre s := by
  implies_sat [Spec.Blowfish.expandKeyContract, Spec.Blowfish.expandKeySig, Spec.Blowfish.expandKeyPre,
    Spec.Blowfish.expandKeyPost, Spec.Blowfish.validKey, X86_64.abi, X86_64.argRegs] [expandKeyFrameSat]
    using expandKeyFrameSat

theorem expandKey_framed :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackScratchWiped 40 .rcx 4 Impl.Blowfish.X86_64.expandKey)
      (Spec.Blowfish.expandKeyContract X86_64.abi 40) :=
  X86_64.Verified.stackScratchWiped (sig := Spec.Blowfish.expandKeySig) (nm := "scratch") (e := .u64)
    (n := 4) (pre := Spec.Blowfish.expandKeyPre X86_64.abi.ptrBits)
    (post := Spec.Blowfish.expandKeyPost X86_64.abi.ptrBits) (wa := false) (stack := 0)
    (bytes := 40) expandKey_verified (by decide) (by decide) (by decide)
    (Code.all_of_spTest (by decide +kernel)) (by decide +kernel) (by decide)
    (Proof.Blowfish.expandKeyPostOut_local _) expandKeyFrameSat_pre

/-- An implementation `c` of ECB in the direction `d`, proved with its
working space as an argument and no stack, in its frame. -/
theorem ecb_framed {c : Prog isa} {d : Spec.Blowfish.Direction}
    (h : Verified X86_64.target c (Proof.Blowfish.ecbScratchContract X86_64.abi d 0))
    (hsp : c.all (fun i => !isa.writesSp i) = true := by exact Code.all_of_spTest (by lit_decide))
    (hd : c.x86_64Depth ≤ 0 := by lit_decide) :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratchWiped 264 .rcx 2 c)
      (Spec.Blowfish.ecbContract X86_64.abi d 264) :=
  X86_64.Verified.stackScratchWiped (sig := Spec.Blowfish.ecbSig) (nm := "scratch") (e := .u64)
    (n := 32) (post := Spec.Blowfish.ecbPost d X86_64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 264) h (by decide) (by decide) (by decide) hsp hd (by decide)
    (Proof.Blowfish.ecbPostOut_local _ d)
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

end VG.Proof.Blowfish.X86_64
