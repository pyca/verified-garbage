module

public import VerifiedGarbage.Proof.AesCbc.Rounds
public import VerifiedGarbage.Impl.AesCbc.X86_64.Vaes512Decrypt
public import VerifiedGarbage.Proof.AesCbc.X86_64.VaesDecrypt
import VerifiedGarbage.Proof.Aes.X86_64.VaesZ.Rounds
import VerifiedGarbage.Proof.Aes.X86_64.VaesZ.Ctr
public import VerifiedGarbage.Proof.Framework.X86_64.ZFrame
import VerifiedGarbage.Proof.Framework.X86_64.Avx512
import VerifiedGarbage.Proof.Framework.X86_64.Reduce
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Impl.AesCbc.X86_64.Vaes512Decrypt
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.Proof.Framework.Taint

-- separate module: the four-lane inverse cipher and CBC loop have their own verification.
/-! # Verified AVX-512 CBC decryption -/

@[expose] public section
namespace VG.Proof.AesCbc.X86_64.Vaes512Decrypt
open VG VG.X86_64 VG.X86_64.RegUpd
open VG.Impl.AesCbc.X86_64.Vaes512Decrypt
open VG.Impl.Aes.X86_64.AesNi (at_ regs8)
open VG.Proof.Aes.X86_64.AesNi
open VG.Proof.AesCbc.X86_64.Decrypt (chaining output)
open VG.Proof.Aes.X86_64.VaesZ (keyOpZ_ok ZFrame.of_keys)
open VG.Spec.Aes (roundKey invCipher addRoundKey)
open VG.Proof.Aes (invMid invMid_succ invCipher_eq)

theorem DKeys.of_zframe {nr : Nat} {w : List Byte} {rs : List XReg} {s s' : State} (h : DKeys nr w s)
    (hf : ZFrame rs s s') : DKeys nr w s' :=
  ⟨ZFrame.of_keys h.keys hf, by rw [hf.rd, hf.wr, hf.gpr, hf.mem]; exact h.imc⟩

/-- Both lanes of each register `b` of `regs` hold the state after `m`
middle rounds of the inverse cipher, from the states `x b l`. -/
def DInv (regs : List XReg) (nr : Nat) (w : List Byte) (x : XReg → Nat → Spec.Aes.State) (m : Nat)
    (s : State) : Prop :=
  ∀ b ∈ regs, ∀ l < 4, st (s.zlane b l) = invMid nr w m (addRoundKey (x b l) (roundKey w nr))

theorem dround_ok (regs : List XReg) (hnd : regs.Nodup) (h8 : .xmm8 ∉ regs) {nr : Nat}
    {w : List Byte} {x : XReg → Nat → Spec.Aes.State} {m : Nat} (hm : m + 1 < nr) {s : State}
    (hK : DKeys nr w s) (hI : DInv regs nr w x m s) :
    WP isa (.block (dround regs (nr - 1 - m))) s fun s' =>
      DInv regs nr w x (m + 1) s' ∧ ZFrame (.xmm8 :: regs) s s' := by
  obtain ⟨hin, hst⟩ := hK.imc (nr - 1 - m) (by omega) (by omega)
  refine WP.mono (keyOpZ_ok .xmm8 regs .vaesdec _ s hnd h8 (by rw [ea_at]; exact hin))
    fun s' ⟨hv, hf⟩ => ⟨fun b hb l hl => ?_, hf⟩
  rw [hv b hb l hl, ea_at]
  show st (XBinOp.eval .aesdec _ _) = _
  rw [aesdec_st _ _ _ hst, hI b hb l hl, invMid_succ]
  rfl

/-- `dround_ok`, with the round key's index given. -/
theorem dround_ok' (regs : List XReg) (hnd : regs.Nodup) (h8 : .xmm8 ∉ regs) {nr : Nat}
    {w : List Byte} {x : XReg → Nat → Spec.Aes.State} {j m : Nat} (hj : j + m + 1 = nr) (hj0 : 0 < j)
    {s : State} (hK : DKeys nr w s) (hI : DInv regs nr w x m s) :
    WP isa (.block (dround regs j)) s fun s' =>
      DInv regs nr w x (m + 1) s' ∧ ZFrame (.xmm8 :: regs) s s' := by
  rw [show j = nr - 1 - m by omega]
  exact dround_ok regs hnd h8 (by omega) hK hI

/-- Middle rounds `nr − 10 … nr − 2`, with round keys `9 … 1`. -/
theorem drounds_ok (regs : List XReg) (hnd : regs.Nodup) (h8 : .xmm8 ∉ regs) {nr : Nat}
    (hnr : 10 ≤ nr) {w : List Byte} {x : XReg → Nat → Spec.Aes.State} (k : Nat) (hk : k ≤ 9) (s : State)
    (hK : DKeys nr w s) (hI : DInv regs nr w x (nr - 10) s) :
    WP isa (.block ((List.range k).flatMap fun j => dround regs (9 - j))) s fun s' =>
      DInv regs nr w x (nr - 10 + k) s' ∧ ZFrame (.xmm8 :: regs) s s' := by
  induction k with
  | zero => rw [List.range_zero, List.flatMap_nil]; exact WP.block_nil ⟨hI, ZFrame.refl _ _⟩
  | succ k ih =>
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun s₁ ⟨hI₁, hf₁⟩ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    exact WP.mono (dround_ok' regs hnd h8 (j := 9 - k) (m := nr - 10 + k) (by omega) (by omega)
        (DKeys.of_zframe hK hf₁) hI₁)
      fun s' ⟨hI', hf'⟩ => ⟨by rw [show nr - 10 + (k + 1) = nr - 10 + k + 1 by omega]; exact hI',
        hf₁.trans hf'⟩

theorem aesDec_ok (regs : List XReg) (hnd : regs.Nodup) (h8 : .xmm8 ∉ regs) {nr : Nat}
    (hnr : nr = 10 ∨ nr = 12 ∨ nr = 14) {w : List Byte} (s : State) (hK : DKeys nr w s)
    (hrsi : s.gpr .rsi = BitVec.ofNat 64 nr)
    (hr10 : s.gpr .r10 = s.gpr .rdi + BitVec.ofNat 64 (16 * nr)) :
    WP isa (aesDec regs) s fun s' =>
      (∀ b ∈ regs, ∀ l < 4, st (s'.zlane b l) = invCipher nr w (st (s.zlane b l))) ∧
      ZFrame (.xmm8 :: regs) s s' := by
  let x : XReg → Nat → Spec.Aes.State := fun b l => st (s.zlane b l)
  have hea : s.ea (at_ .r10 0) = s.gpr .rdi + BitVec.ofInt 64 ((16 * nr : Nat) : Int) := by
    rw [ea_at, hr10, ofInt_natCast, ofInt_natCast]; exact BitVec.add_zero _
  have kR := byte_roundKey s.mem (s.gpr .rdi) (L := 16 * (nr + 1)) (j := nr) (by omega)
  -- `AddRoundKey` with the last round key.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (keyOpZ_ok .xmm8 regs .vpxord _ s hnd h8
      (by rw [hea]; exact hK.keys.keys nr (Nat.le_refl _)))
    fun s₁ ⟨hv₁, hf₁⟩ => ?_
  have hI₁ : DInv regs nr w x 0 s₁ := fun b hb l hl => by
    rw [hv₁ b hb l hl]
    show st (XBinOp.eval .pxor _ _) = _
    rw [pxor_st _ _ (roundKey w nr) (by rw [hK.keys.sched, hea]; exact kR)]; rfl
  refine WP.mono (VG.Proof.Aes.X86_64.VaesZ.cmpRsiZ_ok s₁ 10 nr (by rw [hf₁.gpr, hrsi])) fun s₁' ⟨hz₁, hf₁'⟩ => ?_
  have hf₁₁ := hf₁.trans (hf₁'.mono (by simp))
  have hI₁' : DInv regs nr w x 0 s₁' := fun b hb l hl => by
    rw [hf₁'.zlane b (by simp) l hl]; exact hI₁ b hb l hl
  -- The middle rounds with round keys `nr − 1 … 10`.
  have h₂ : WP isa (.ite .e (.block [])
        (.seq (.block [.alu .cmp .rsi (.imm 12)])
          (.seq (.ite .e (.block []) (.block (dround regs 13 ++ dround regs 12)))
            (.block (dround regs 11 ++ dround regs 10))))) s₁' fun s' =>
        DInv regs nr w x (nr - 10) s' ∧ ZFrame (.xmm8 :: regs) s s' := by
    have hrsi₁ : s₁'.gpr .rsi = BitVec.ofNat 64 nr := by rw [hf₁₁.gpr, hrsi]
    rcases hnr with rfl | rfl | rfl
    · exact WP.ite true (by simp [eval, hz₁]) (fun _ => WP.block_nil ⟨hI₁', hf₁₁⟩)
        (fun h => absurd h (by decide))
    · -- 12 rounds: round keys 11 and 10.
      refine WP.ite false (by simp [eval, hz₁]) (fun h => absurd h (by decide)) fun _ => ?_
      refine WP.seq (WP.mono (VG.Proof.Aes.X86_64.VaesZ.cmpRsiZ_ok s₁' 12 _ hrsi₁) fun s₂ ⟨hz₂, hf₂⟩ => ?_)
      have hI₂ : DInv regs 12 w x 0 s₂ := fun b hb l hl => by
        rw [hf₂.zlane b (by simp) l hl]; exact hI₁' b hb l hl
      have hf₁₂ := hf₁₁.trans (hf₂.mono (by simp))
      refine WP.seq ?_
      refine WP.mono (Q := fun s' => DInv regs 12 w x 0 s' ∧ ZFrame (.xmm8 :: regs) s s') ?_
        fun s₃ ⟨hI₃, hf₃⟩ => ?_
      · refine WP.ite true (by simp [eval, hz₂]) (fun _ => ?_) (fun h => absurd h (by decide))
        exact WP.block_nil (show DInv regs 12 w x 0 s₂ ∧ ZFrame (.xmm8 :: regs) s s₂ from ⟨hI₂, hf₁₂⟩)
      rw [WP.block_append_iff]
      refine WP.mono (dround_ok' regs hnd h8 (j := 11) (m := 0) (by omega) (by omega)
          (DKeys.of_zframe hK hf₃) hI₃)
        fun s₄ ⟨hI₄, hf₄⟩ => ?_
      exact WP.mono (dround_ok' regs hnd h8 (j := 10) (m := 1) (by omega) (by omega)
        (DKeys.of_zframe hK (hf₃.trans hf₄)) hI₄) fun s' ⟨hI', hf'⟩ => ⟨hI', hf₃.trans (hf₄.trans hf')⟩
    · -- 14 rounds: round keys 13, 12, 11 and 10.
      refine WP.ite false (by simp [eval, hz₁]) (fun h => absurd h (by decide)) fun _ => ?_
      refine WP.seq (WP.mono (VG.Proof.Aes.X86_64.VaesZ.cmpRsiZ_ok s₁' 12 _ hrsi₁) fun s₂ ⟨hz₂, hf₂⟩ => ?_)
      have hI₂ : DInv regs 14 w x 0 s₂ := fun b hb l hl => by
        rw [hf₂.zlane b (by simp) l hl]; exact hI₁' b hb l hl
      have hf₁₂ := hf₁₁.trans (hf₂.mono (by simp))
      have hK₂ := DKeys.of_zframe hK hf₁₂
      refine WP.seq ?_
      refine WP.mono (Q := fun s' => DInv regs 14 w x 2 s' ∧ ZFrame (.xmm8 :: regs) s s') ?_
        fun s₃ ⟨hI₃, hf₃⟩ => ?_
      · refine WP.ite false (by simp [eval, hz₂]) (fun h => absurd h (by decide)) fun _ => ?_
        rw [WP.block_append_iff]
        refine WP.mono (dround_ok' regs hnd h8 (j := 13) (m := 0) (by omega) (by omega) hK₂ hI₂)
          fun s₃ ⟨hI₃, hf₃⟩ => ?_
        exact WP.mono (dround_ok' regs hnd h8 (j := 12) (m := 1) (by omega) (by omega)
            (DKeys.of_zframe hK₂ hf₃) hI₃)
          fun s' ⟨hI', hf'⟩ => (⟨hI', hf₁₂.trans (hf₃.trans hf')⟩ :
            DInv regs 14 w x (1 + 1) s' ∧ ZFrame (.xmm8 :: regs) s s')
      · rw [WP.block_append_iff]
        refine WP.mono (dround_ok' regs hnd h8 (j := 11) (m := 2) (by omega) (by omega)
            (DKeys.of_zframe hK hf₃) hI₃)
          fun s₄ ⟨hI₄, hf₄⟩ => ?_
        exact WP.mono (dround_ok' regs hnd h8 (j := 10) (m := 3) (by omega) (by omega)
          (DKeys.of_zframe hK (hf₃.trans hf₄)) hI₄) fun s' ⟨hI', hf'⟩ => ⟨hI', hf₃.trans (hf₄.trans hf')⟩
  refine WP.seq (WP.mono h₂ fun s₂ ⟨hI₂, hf₂⟩ => ?_)
  -- Round keys `9 … 1`, and the last round.
  have hK₂ := DKeys.of_zframe hK hf₂
  have hnr' : 10 ≤ nr := by rcases hnr with h | h | h <;> omega
  rw [WP.block_append_iff]
  refine WP.mono (drounds_ok regs hnd h8 hnr' 9 (by omega) s₂ hK₂ hI₂) fun s₃ ⟨hI₃, hf₃⟩ => ?_
  have hK₃ := DKeys.of_zframe hK₂ hf₃
  have k0 := byte_roundKey s₃.mem (s₃.gpr .rdi) (L := 16 * (nr + 1)) (j := 0) (by omega)
  simp only [Nat.mul_zero] at k0
  refine WP.mono (keyOpZ_ok .xmm8 regs .vaesdeclast _ s₃ hnd h8
      (by rw [ea_at]; exact hK₃.keys.keys 0 (by omega)))
    fun s' ⟨hv, hf'⟩ => ⟨fun b hb l hl => ?_, hf₂.trans (hf₃.trans hf')⟩
  rw [hv b hb l hl]
  show st (XBinOp.eval .aesdeclast _ _) = _
  rw [aesdeclast_st _ _ (roundKey w 0) (by rw [hK₃.keys.sched, ea_at]; exact k0), hI₃ b hb l hl,
    invCipher_eq, show nr - 10 + 9 = nr - 1 by omega]


theorem load1_ok (b : XReg) (d : Nat) (s : State)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofInt 64 (d : Int)) 64) :
    WP isa (.block [.vmovdqu32Load b (at_ .rdx d)]) s fun t =>
      (∀ l < 4, t.zlane b l = s.mem.readW
        (s.gpr .rdx + BitVec.ofInt 64 (d : Int) + BitVec.ofNat 64 (16*l)) 128) ∧
      t.gpr = s.gpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ r, r ≠ b → ∀ l < 4, t.zlane r l = s.zlane r l) := by
  let a := s.gpr .rdx + BitVec.ofInt 64 (d : Int)
  let v := s.mem.readW a 512
  rw [WP.block_cons_iff]
  refine ⟨s.setZ b (v.extractLsb' 0 128) (v.extractLsb' 128 128)
      (v.extractLsb' 256 128) (v.extractLsb' 384 128), by
    simp only [isa,exec,State.load512,ea_at,hin,ite_true,Option.map_some]; rfl, WP.block_nil ?_⟩
  refine ⟨fun l hl => ?_,by simp,by simp,by simp,by simp,fun r hr l hl => ?_⟩
  · rw [State.zlane_setZ _ _ _ _ _ _ _ hl]
    simp only [ite_true]
    rw [pick4_lanes (fun i => v.extractLsb' (128*i) 128) hl]
    exact VG.Proof.Aes.X86_64.VaesZ.load512_lane _ _ hl
  · simp only [State.zlane_setZ _ _ _ _ _ _ _ hl,ite_eq_right hr]

theorem loadData_ok (regs : List XReg) (j : Nat) (s : State) (hnd : regs.Nodup)
    (hin : ∀ k < regs.length,
      InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofInt 64 ((64 * (j + k) : Nat) : Int)) 64) :
    WP isa (.block (loadData regs j)) s fun s' =>
      (∀ k (h : k < regs.length), ∀ l < 4,
        st (s'.zlane regs[k] l) =
          Spec.Aes.stateAt s.mem (s.gpr .rdx + BitVec.ofNat 64 (16 * (4 * (j + k) + l)))) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ∉ regs → ∀ l < 4, s'.zlane r l = s.zlane r l) := by
  induction regs generalizing j s with
  | nil => exact WP.block_nil ⟨fun _ h => absurd h (by simp), rfl, rfl, rfl, rfl, fun _ _ _ _ => rfl⟩
  | cons b bs ih =>
    have hbs : b ∉ bs := (List.nodup_cons.mp hnd).1
    simp only [List.length_cons] at hin
    rw [loadData, ← List.singleton_append, WP.block_append_iff]
    have hin0 := hin 0 (by omega_arith)
    rw [Nat.add_zero] at hin0
    refine WP.mono (load1_ok b (64*j) s hin0) fun s₁ ⟨hv₁,g₁,m₁,rd₁,wr₁,o₁⟩ => ?_
    refine WP.mono (ih (j+1) s₁ (List.nodup_cons.mp hnd).2 (fun k hk => by
        rw [rd₁,wr₁,g₁,show j+1+k=j+(k+1) by omega_arith]; exact hin (k+1) (by omega_arith)))
      fun s' ⟨hb,g,m,rd,wr,hx⟩ => ?_
    rw [g₁,m₁] at hb
    refine ⟨fun k hk l hl => ?_,g.trans g₁,m.trans m₁,rd.trans rd₁,wr.trans wr₁,fun r hr l hl => ?_⟩
    · cases k with
      | zero =>
        simp only [List.getElem_cons_zero,Nat.add_zero]
        rw [hx b hbs l hl,hv₁ l hl,stateAt_eq,ofInt_natCast,
          Offset.add_add_eq _ (c := 16*(4*j+l)) (by omega_arith)]
      | succ k =>
        simp only [List.getElem_cons_succ]
        rw [hb k (by simpa using hk) l hl,show j+1+k=j+(k+1) by omega_arith]
    · simp only [List.mem_cons,not_or] at hr
      rw [hx r hr.2 l hl,o₁ r hr.1 l hl]


/-- Legacy 128-bit moves retain the other three lanes. -/
theorem zlane_setXmm (s : State) (d r : XReg) (v : BitVec 128) (l : Nat) :
    (s.setXmm d v).zlane r l = if r=d ∧ l=0 then v else s.zlane r l := by
  have hy : (s.setXmm d v).ymmHi = s.ymmHi := rfl
  have hz : (s.setXmm d v).zmmHi = s.zmmHi := rfl
  by_cases hr : r=d
  · subst hr
    by_cases hl : l=0
    · subst hl; simp [State.zlane,State.lane,xmm_setXmm_self]
    · simp [State.zlane,State.lane,hl,hy,hz]
  · by_cases hl : l=0
    · subst hl; simp [State.zlane,State.lane,xmm_setXmm_of_ne _ _ hr,hr]
    · simp [State.zlane,State.lane,hl,hy,hz]

def feedback (s : State) (a : Addr) (l : Nat) : BitVec 128 :=
  if l=0 then s.xmm .xmm15 else s.mem.readW (a + BitVec.ofNat 64 (16*(l-1))) 128

/-- Four blocks share one feedback XOR and one store. -/
theorem finish4_ok (b : XReg) (j : Nat) (s : State) (h14 : b ≠ .xmm14) (h15 : b ≠ .xmm15)
    (hin : InRegions s.wr (s.gpr .rdx + BitVec.ofInt 64 ((64*j : Nat) : Int)) 64) :
    WP isa (.block (finish4 b j)) s fun t =>
      (∃ v : BitVec 512, t.mem = s.mem.writeW (s.gpr .rdx + BitVec.ofInt 64 ((64*j : Nat) : Int)) v ∧
        ∀ l < 4, st (v.extractLsb' (128*l) 128) =
          st (s.zlane b l ^^^ feedback s (s.gpr .rdx + BitVec.ofInt 64 ((64*j : Nat) : Int)) l)) ∧
      t.xmm .xmm15 = s.mem.readW (s.gpr .rdx + BitVec.ofInt 64 ((64*j : Nat) : Int) + 48) 128 ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ r, r ≠ b → r ≠ .xmm14 → r ≠ .xmm15 → ∀ l < 4, t.zlane r l = s.zlane r l) := by
  rw [finish4,← List.singleton_append,WP.block_append_iff]
  refine WP.mono (load1_ok .xmm14 (64*j) s (inRegions_wr hin)) fun u ⟨hu,gu,mu,ru,wu,ou⟩ => ?_
  let v := (ZOp.vshufi32x4 .xmm14 .xmm14 .xmm14 144).exec u
  let w := v.setXmm .xmm14 (v.xmm .xmm15)
  let a := s.gpr .rdx + BitVec.ofInt 64 ((64*j : Nat) : Int)
  let x := w.setXmm .xmm15 (s.mem.readW (a+48) 128)
  let y := (ZOp.zbin .vpxord b b .xmm14).exec x
  have vg : v.gpr = s.gpr := (ZOp.exec_gpr _ _).trans gu
  have vm : v.mem = s.mem := (ZOp.exec_mem _ _).trans mu
  have vr : v.rd = s.rd := (ZOp.exec_rd _ _).trans ru
  have vw : v.wr = s.wr := (ZOp.exec_wr _ _).trans wu
  have ea15 : w.ea (at_ .rdx (64*j+48)) = a+48 := by
    simp only [w,ea_at,gpr_setXmm,vg,a,ofInt_natCast]
    change s.gpr .rdx + BitVec.ofNat 64 (64*j+48) = s.gpr .rdx + BitVec.ofNat 64 (64*j) + BitVec.ofNat 64 48
    exact (Offset.add_add_eq _ (c := 64*j+48) (by omega_arith)).symm
  have hin15 : InRegions (w.rd ++ w.wr) (w.gpr .rdx + BitVec.ofNat 64 (64*j+48)) 16 := by
    change InRegions (w.rd ++ w.wr) (w.ea (at_ .rdx (64*j+48))) 16
    rw [ea15]
    simp only [w,rd_setXmm,wr_setXmm,vr,vw]
    obtain ⟨r,hr,hc⟩ := hin
    refine ⟨r,List.mem_append_right _ hr,?_⟩
    change (a-r.base).toNat+64 ≤ r.len at hc
    change (a+48-r.base).toNat+16 ≤ r.len
    bv_omega
  rw [WP.block_cons_iff]
  refine ⟨v,rfl,?_⟩
  rw [WP.block_cons_iff]
  refine ⟨w,rfl,?_⟩
  rw [WP.block_cons_iff]
  refine ⟨x,by
    have he := VG.Proof.AesCbc.X86_64.Encrypt.exec_load (b := .xmm15) (r := .rdx) (d := 64*j+48) hin15
    have ha : w.gpr .rdx + BitVec.ofNat 64 (64*j+48) = a+48 := ea15
    simpa only [ha,w,mem_setXmm,vm,x,Impl.CmacAes.X86_64.AesNi.at_,Impl.Aes.X86_64.AesNi.at_] using he,?_⟩
  rw [WP.block_cons_iff]
  refine ⟨y,rfl,?_⟩
  rw [WP.block_cons_iff]
  have yg : y.gpr = s.gpr := by simp only [y,x,w,ZOp.exec_gpr,gpr_setXmm,vg]
  have ym : y.mem = s.mem := by simp only [y,x,w,ZOp.exec_mem,mem_setXmm,vm]
  have yr : y.rd = s.rd := by simp only [y,x,w,ZOp.exec_rd,rd_setXmm,vr]
  have yw : y.wr = s.wr := by simp only [y,x,w,ZOp.exec_wr,wr_setXmm,vw]
  refine ⟨y.setMem (s.mem.writeW a (y.zmm b)),by
    simp only [isa,exec,State.store512_eq,ea_at,yg,yw,ym,hin,ite_true,a],WP.block_nil ?_⟩
  have keep (r : XReg) (hr14 : r ≠ .xmm14) (hr15 : r ≠ .xmm15) (l : Nat) (hl : l<4) :
      x.zlane r l = s.zlane r l := by
    simp only [x,w,zlane_setXmm,ite_eq_right (show ¬(r=.xmm15 ∧ l=0) by simp [hr15]),
      ite_eq_right (show ¬(r=.xmm14 ∧ l=0) by simp [hr14])]
    rw [zlane_vshufi32x4 _ _ _ _ _ _ hl,ite_eq_right hr14,ou r hr14 l hl]
  have feed (l : Nat) (hl : l<4) : x.zlane .xmm14 l = feedback s a l := by
    simp only [x,w,zlane_setXmm,show (XReg.xmm14 ≠ .xmm15) from by decide,false_and,ite_false,true_and]
    by_cases he : l=0
    · subst he
      simp only [ite_true,feedback]
      rw [← show v.zlane .xmm15 0 = v.xmm .xmm15 from rfl,
        zlane_vshufi32x4 _ _ _ _ _ _ (by decide),ite_eq_right (by decide),ou _ (by decide) 0 (by decide)]
      rfl
    · rw [ite_eq_right he,zlane_vshufi32x4 _ _ _ _ _ _ hl,ite_eq_left rfl]
      have hs : shuf4Lanes (u.zlane .xmm14) (u.zlane .xmm14) 144 l = u.zlane .xmm14 (l-1) := by
        have hf : ∀ i : Fin 4, i.1 ≠ 0 → ((144 : BitVec 8).extractLsb' (2*i.1) 2).toNat = i.1-1 := by decide
        simp only [shuf4Lanes,ite_self,hf ⟨l,hl⟩ he]
      rw [hs,hu _ (by omega_arith),feedback,ite_eq_right he]
  refine ⟨⟨y.zmm b,rfl,fun l hl => ?_⟩,?_,yg,yr,yw,fun r hb hr14 hr15 l hl => ?_⟩
  · rw [VG.Proof.Aes.X86_64.VaesZ.zmm_lane _ _ hl,zlane_zbin _ _ _ _ _ _ hl,ite_eq_left rfl,keep b h14 h15 l hl,feed l hl]
    rfl
  · change y.zlane .xmm15 0 = _
    rw [zlane_zbin _ _ _ _ _ _ (by decide),ite_eq_right (Ne.symm h15)]
    exact xmm_setXmm_self _ _ _
  · rw [State.setMem_zlane,zlane_zbin _ _ _ _ _ _ hl,ite_eq_right hb,keep r hr14 hr15 l hl]


theorem data_write4 {m₀ m : Mem} {D : Addr} {n c : Nat} {F : Nat → Spec.Aes.State} {v : BitVec 512}
    (hn : 16*n ≤ 2^64) (hc : c+4 ≤ n) (hd : Decrypt.DataInv m₀ m D n c F)
    (hv : ∀ l < 4, st (v.extractLsb' (128*l) 128) = F (c+l)) :
    Decrypt.DataInv m₀ (m.writeW (D + BitVec.ofNat 64 (16*c)) v) D n (c+4) F := by
  intro k hk
  by_cases h : c ≤ k ∧ k < c+4
  · rw [ite_eq_left h.2,stateAt_eq]
    have ea : D+BitVec.ofNat 64 (16*k) = D+BitVec.ofNat 64 (16*c)+BitVec.ofNat 64 (16*(k-c)) :=
      (Offset.add_add_eq _ (by omega_arith)).symm
    rw [ea,readW_writeW_inside m _ v (k := 16*(k-c)) (n := 16) (by omega_arith) (by decide),
      show 8*(16*(k-c))=128*(k-c) by omega_arith,hv _ (by omega_arith),show c+(k-c)=k by omega_arith]
  · rw [stateAt_eq,Mem.readW_writeW_sep
      (Offset.disjoint D (by omega_using [h]) (by omega_arith) (by omega_arith)) (by decide),← stateAt_eq,hd k hk]
    by_cases hlt : k<c
    · rw [ite_eq_left hlt,ite_eq_left (by omega_arith)]
    · rw [ite_eq_right hlt,ite_eq_right (by omega_using [h,hlt])]

theorem finishData_ok {m₀ : Mem} {D : Addr} {n c : Nat} {F : Nat → Spec.Aes.State}
    {chain : Nat → BitVec 128} (hn : 16*n ≤ 2^64)
    (hnext : ∀ k < n, chain (k+1) = m₀.readW (D+BitVec.ofNat 64 (16*k)) 128) :
    ∀ (rs : List XReg) (j : Nat) (s : State), rs.Nodup → .xmm14 ∉ rs → .xmm15 ∉ rs →
    s.gpr .rdx = D+BitVec.ofNat 64 (16*c) → c+4*j+4*rs.length ≤ n →
    (⟨D,16*n⟩ : Region) ∈ s.wr → Decrypt.DataInv m₀ s.mem D n (c+4*j) F →
    s.xmm .xmm15 = chain (c+4*j) →
    (∀ k (h : k<rs.length), ∀ l<4, st (s.zlane rs[k] l ^^^ chain (c+4*(j+k)+l)) = F (c+4*(j+k)+l)) →
    WP isa (.block (finishData rs j)) s fun t =>
      Decrypt.DataInv m₀ t.mem D n (c+4*j+4*rs.length) F ∧
      t.xmm .xmm15 = chain (c+4*j+4*rs.length) ∧ Frame [⟨D,16*n⟩] s.mem t.mem ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ r, r ≠ .xmm15 → r ≠ .xmm14 → r ∉ rs → ∀ l<4, t.zlane r l = s.zlane r l)
  | [], _, s, _, _, _, _, _, _, hd, hx, _ =>
    WP.block_nil ⟨by simpa using hd,by simpa using hx,Frame.refl _ _,rfl,rfl,rfl,fun _ _ _ _ _ _ => rfl⟩
  | b::bs, j, s, hnd, h14, h15, hg, hc, hw, hd, hx, hv => by
    simp only [List.length_cons] at hc
    have hb14 : b ≠ .xmm14 := fun h => h14 (h ▸ List.mem_cons_self)
    have hb15 : b ≠ .xmm15 := fun h => h15 (h ▸ List.mem_cons_self)
    have hbs : b ∉ bs := (List.nodup_cons.mp hnd).1
    have h14' : .xmm14 ∉ bs := fun h => h14 (List.mem_cons_of_mem _ h)
    have h15' : .xmm15 ∉ bs := fun h => h15 (List.mem_cons_of_mem _ h)
    have ea : s.gpr .rdx+BitVec.ofInt 64 ((64*j : Nat) : Int) = D+BitVec.ofNat 64 (16*(c+4*j)) := by
      rw [hg,ofInt_natCast,Offset.add_add_eq _ (c := 16*(c+4*j)) (by omega_arith)]
    have ea3 : s.gpr .rdx+BitVec.ofInt 64 ((64*j : Nat) : Int)+48 = D+BitVec.ofNat 64 (16*(c+4*j+3)) := by
      rw [ea]
      exact Offset.add_add_eq _ (a := 16*(c+4*j)) (b := 48) (by omega_arith)
    rw [finishData,WP.block_append_iff]
    refine WP.mono (finish4_ok b j s hb14 hb15 (by
      rw [ea]; exact ⟨_,hw,Offset.contains_base _ (by omega_arith) (by omega_arith)⟩))
      fun u ⟨⟨v,hm,hv'⟩,hxu,gu,ru,wu,ou⟩ => ?_
    have hvalues : ∀ l<4, st (v.extractLsb' (128*l) 128) = F (c+4*j+l) := by
      intro l hl
      rw [hv' l hl]
      have hfeed : feedback s (s.gpr .rdx+BitVec.ofInt 64 ((64*j:Nat):Int)) l = chain (c+4*j+l) := by
        by_cases he : l=0
        · subst he; simpa [feedback] using hx
        · rw [feedback,ite_eq_right he,ea,
            Offset.add_add_eq _ (c := 16*(c+4*j+l-1)) (by omega_arith),
            Decrypt.original_word hd (by omega_arith) (by omega_arith),
            ← hnext (c+4*j+l-1) (by omega_arith)]
          congr 1 <;> omega_arith
      rw [hfeed]
      exact hv 0 (by simp) l hl
    rw [ea] at hm
    have hd' := data_write4 hn (by omega_arith) hd hvalues
    rw [← hm] at hd'
    have hchain : u.xmm .xmm15 = chain (c+4*(j+1)) := by
      rw [hxu,ea3,Decrypt.original_word hd (by omega_arith) (by omega_arith),
        ← hnext (c+4*j+3) (by omega_arith)]
      congr 1 <;> omega_arith
    have hf : Frame [⟨D,16*n⟩] s.mem u.mem := by
      rw [hm]
      exact (Frame.refl _ _).writeW List.mem_cons_self _
        (Offset.contains_base _ (by omega_arith) (by omega_arith))
    refine WP.mono (finishData_ok (m₀ := m₀) (D := D) (n := n) (c := c) (F := F) (chain := chain)
      hn hnext bs (j+1) u (List.nodup_cons.mp hnd).2 h14' h15'
      (by rw [gu]; exact hg) (by omega_arith) (wu ▸ hw)
      (by simpa [Nat.mul_add,Nat.add_assoc] using hd') hchain
      (fun k hk l hl => by
        rw [ou _ (fun h => hbs (h ▸ List.getElem_mem hk)) (fun h => h14' (h ▸ List.getElem_mem hk))
          (fun h => h15' (h ▸ List.getElem_mem hk)) l hl]
        have he := hv (k+1) (by simp; omega_arith) l hl
        simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using he))
      fun t ⟨hdt,hxt,hft,gt,rt,wt,ot⟩ => ?_
    have he : c+4*(j+1)+4*bs.length = c+4*j+4*(b::bs).length := by simp; omega_arith
    rw [he] at hdt hxt
    exact ⟨hdt,hxt,hf.trans hft,gt.trans gu,rt.trans ru,wt.trans wu,
      fun r h₁ h₂ h₃ l hl => (ot r h₁ h₂ (fun h => h₃ (List.mem_cons_of_mem _ h)) l hl).trans
        (ou r (fun h => h₃ (h ▸ List.mem_cons_self)) h₂ h₁ l hl)⟩

theorem group32_ok {s₀ s : State} (hp : UPre s₀) {c : Nat} (hc : c+32 ≤ N s₀)
    (hI : Decrypt.Inv s₀ c c s) (after : List Instr) {Q : State → Prop}
    (hQ : ∀ t, Decrypt.Inv s₀ (c+32) c t → WP isa (.block after) t Q) :
    WP isa (.seq (.block (loadData regs8 0))
      (.seq (aesDec regs8) (.block (finishData regs8 0 ++ after)))) s Q := by
  have hnd : regs8.Nodup := by decide
  have hw := hp.data_wrap
  have addr (k l : Nat) :
      s.gpr .rdx + BitVec.ofNat 64 (16*(4*(0+k)+l)) = blk s₀ (c+4*k+l) := by
    rw [hI.rdx,blk,blk,Offset.add_add_eq _ (c := 16*(c+4*k+l)) (by omega_arith)]
  refine WP.seq (WP.mono (loadData_ok regs8 0 s hnd (fun k hk => by
    have hk' : k < 8 := hk
    rw [ofInt_natCast,hI.rdx,blk,Offset.add_add_eq _ (c := 16*c+64*(0+k)) (by omega_arith),hI.rd,hI.wr,hp.rd,hp.wr]
    exact ⟨dataR s₀,by simp,Offset.contains_base _ (by omega_arith) (by omega_arith)⟩))
    fun u ⟨hl,gl,ml,rl,wl,xl⟩ => ?_)
  have hku : DKeys (R s₀) (wK s₀) u :=
    Ecb.dkeys_congr hI.keys (by rw [gl]) (by rw [gl]) rl wl (by rw [ml]) (fun _ _ _ => by rw [ml])
  refine WP.seq (WP.mono (aesDec_ok regs8 hnd (by decide) hp.rounds u hku
    (by rw [gl,hI.rsi]; simp) (by rw [gl,hI.r10,hI.rdi])) fun v ⟨ha,fa⟩ => ?_)
  have gv : v.gpr = s.gpr := fa.gpr.trans gl
  have mv : v.mem = s.mem := fa.mem.trans ml
  have hx : v.xmm .xmm15 = chaining s₀ c := by
    rw [← show v.zlane .xmm15 0 = v.xmm .xmm15 from rfl,fa.zlane _ (by decide) 0 (by decide),
      xl _ (by decide) 0 (by decide)]
    exact hI.chain
  rw [WP.block_append_iff]
  refine WP.mono (finishData_ok (m₀ := s₀.mem) (D := Dp s₀) (n := N s₀) (c := c)
    (F := output s₀) (chain := chaining s₀) (by omega_arith) (fun _ _ => rfl) regs8 0 v hnd
    (by decide) (by decide) (by rw [gv,hI.rdx]) (by change c+32 ≤ N s₀; exact hc)
    (by rw [fa.wr,wl,hI.wr,hp.wr]; simp) (by simpa [mv] using hI.data) (by simpa using hx)
    (fun k hk l hll => by
      have hk' : k < 8 := hk
      have he := ha _ (List.getElem_mem hk) l hll
      rw [hl k hk l hll,addr k l,hI.data _ (by omega_arith),ite_eq_right (by omega_arith)] at he
      apply st_ext
      intro i hi
      rw [getD_st _ hi,byte_xor,← getD_st _ hi,he]
      change _ = (Vector.ofFn fun i =>
        (Spec.Aes.invCipher (R s₀) (wK s₀) (Spec.Aes.stateAt s₀.mem (blk s₀ (c+4*(0+k)+l)))).getD i.1 0 ^^^
          byte (chaining s₀ (c+4*(0+k)+l)) i.1).getD i 0
      rw [getD_ofFn hi]; simp only [Nat.zero_add])) fun t ⟨hd,hchain,hf,hg,hr,hw,_⟩ => ?_
  have gt : t.gpr = s.gpr := hg.trans gv
  have rt : t.rd = s.rd := hr.trans (fa.rd.trans rl)
  have wt : t.wr = s.wr := hw.trans (fa.wr.trans wl)
  rw [mv] at hf
  refine hQ t ⟨hc,Decrypt.keys_stable hp hI.keys hI.rdi hI.r8 gt rt wt hf,
    by rw [gt]; exact hI.rdi,by rw [gt]; exact hI.rsi,by rw [gt]; exact hI.r8,
    by rw [gt]; exact hI.r10,by rw [gt]; exact hI.r11,by rw [gt]; exact hI.rdx,
    by rw [gt]; exact hI.rcx,by exact hchain,by exact hd,
    hI.frame.trans (hf.mono (by simp)),rt.trans hI.rd,wt.trans hI.wr⟩


/-- The thirty-two-block body. -/
theorem body32_ok {s₀ : State} (hp : UPre s₀) {c : Nat} (hc : c + 32 ≤ N s₀) {s : State} (hI : Decrypt.Inv s₀ c c s) :
    WP isa blocks32 s fun s' => Decrypt.Inv s₀ (c + 32) (c + 32) s' ∧
      s'.cf = some (decide (N s₀ - (c + 32) < 32)) := by
  have hn : 16*N s₀ ≤ 2^64 := by have := hp.data_wrap; omega_arith
  refine group32_ok hp hc hI _ fun s₁ hI₁ => ?_
  have e512 : BitVec.signExtend 64 (512 : BitVec 32) = 512 := by decide
  have e32 : BitVec.signExtend 64 (32 : BitVec 32) = 32 := by decide
  have hrdx := hI₁.rdx
  have hrcx := hI₁.rcx
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, arithFlags, State.setFlags, isa, State.setReg, e512, e32, hrdx, hrcx,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  have hsub : BitVec.ofNat 64 (N s₀ - c) - 32 = BitVec.ofNat 64 (N s₀ - (c + 32)) := by
    have := (s₀.gpr .rcx).isLt; bv_omega
  refine ⟨{ hI₁ with
    keys := Ecb.dkeys_congr hI₁.keys (by simp) (by simp) rfl rfl rfl (fun _ _ _ => rfl)
    rdi := by simp [hI₁.rdi]
    rsi := by simp [hI₁.rsi]
    r8 := by simp [hI₁.r8]
    r11 := by simp [hI₁.r11]
    r10 := by simp [hI₁.r10]
    rdx := by simp only [reduceCtorEq, ↓reduceIte, blk]; bv_omega
    rcx := by simp only [ite_true, reduceCtorEq, ite_false]; exact hsub }, ?_⟩
  simp only [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show N s₀ - (c + 32) < 2 ^ 64 by omega_arith),
    show (32 : BitVec 64).toNat = 32 from rfl]


theorem compare32_ok {s₀ s : State} {c : Nat} (hI : Decrypt.Inv s₀ c c s) :
    WP isa (.block [.alu .cmp .rcx (.imm 32)]) s fun t =>
      Decrypt.Inv s₀ c c t ∧ t.cf = some (decide (N s₀-c < 32)) := by
  apply WP.of_runBlock
  have e32 : BitVec.signExtend 64 (32 : BitVec 32) = 32 := by decide
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,execAlu,readSrc,arithFlags,
    State.setFlags,isa,e32,Option.bind_some,Option.some.injEq,exists_eq_left']
  refine ⟨{ hI with keys := hI.keys.of_frame (rs := []) ⟨rfl,rfl,rfl,rfl,fun _ _ => rfl⟩ },?_⟩
  rw [hI.rcx,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have hn : N s₀ < 2^64 := (s₀.gpr .r8).isLt; omega_arith)]
  rfl

theorem wide_ok {s₀ : State} (hp : UPre s₀) {c₀ : Nat} {s : State} (hI : Decrypt.Inv s₀ c₀ c₀ s)
    (hcf : s.cf = some (decide (N s₀-c₀ < 32))) :
    WP isa (.ite .b (.block []) (.loop blocks32 .ae)) s fun t =>
      ∃ c, N s₀-c < 32 ∧ Decrypt.Inv s₀ c c t := by
  refine WP.ite (decide (N s₀-c₀ < 32)) (by simp [eval,hcf]) (fun h => ?_) (fun h => ?_)
  · exact WP.block_nil ⟨c₀,by simpa using h,hI⟩
  · let I32 : Nat → State → Prop := fun m t =>
      ∃ c, m=N s₀-c ∧ c+32 ≤ N s₀ ∧ Decrypt.Inv s₀ c c t
    have hs : ∀ m t, I32 m t → WP isa blocks32 t fun t' =>
        (eval .ae t'=some false ∧ ∃ c, N s₀-c < 32 ∧ Decrypt.Inv s₀ c c t') ∨
        (eval .ae t'=some true ∧ ∃ m' < m, I32 m' t') := by
      rintro m t ⟨c,rfl,hc,hi⟩
      refine WP.mono (body32_ok hp hc hi) fun t' ⟨hi',hcf'⟩ => ?_
      by_cases hh : N s₀-(c+32) < 32
      · exact .inl ⟨by simp [eval,hcf',hh],c+32,hh,hi'⟩
      · exact .inr ⟨by simp [eval,hcf',hh],N s₀-(c+32),by omega_arith,c+32,rfl,by omega_arith,hi'⟩
    exact WP.loop (M := isa) I32 hs (N s₀-c₀) s ⟨c₀,rfl,by simp at h; omega_arith,hI⟩

theorem correct_wp {s₀ : State} (hp : UPre s₀) : WP isa decrypt s₀ fun t =>
    (cbcX86_64 false).post s₀ t ∧ Frame [ivR s₀,dataR s₀,⟨S s₀,224⟩] s₀.mem t.mem := by
  refine WP.seq (WP.mono (Decrypt.setup_ok hp) fun s ⟨hI,_⟩ => ?_)
  refine WP.seq (WP.mono (compare32_ok hI) fun u ⟨hIu,hcf⟩ => ?_)
  refine WP.seq (WP.mono (wide_ok hp hIu hcf) fun v ⟨c,_,hIv⟩ => ?_)
  refine WP.seq (WP.mono (VaesDecrypt.compare16_ok hIv) fun u₁ ⟨hI₁,hcf₁⟩ => ?_)
  refine WP.seq (WP.mono (VaesDecrypt.wide_ok hp hI₁ hcf₁) fun v₁ ⟨_,_,hI₂⟩ => ?_)
  refine WP.seq (WP.mono (VaesDecrypt.exit_ok hI₂) fun w ⟨hIw,hcfw⟩ => ?_)
  exact WP.seq (WP.mono (Decrypt.tail_ok hp hIw hcfw) fun t hi => Decrypt.finish_wp hp hi)

theorem spSafe : decrypt.all (fun i => !isa.writesSp i) = true := by decide +kernel

theorem keeps (r : Reg) (hr : r ∈ calleeSaved) : ∀ i ∈ instrs decrypt, Taint.clobbers i r = false := by
  have h : decrypt.allInstrs (fun i => calleeSaved.all fun r => !Taint.clobbers i r) = true := by
    decide +kernel
  rw [Code.allInstrs_eq,List.all_eq_true] at h
  intro i hi
  simpa using List.all_eq_true.mp (h i hi) r hr

theorem correct (s : State) (hs : (cbcX86_64 false).pre s) :
    ∃ tr t, Exec isa decrypt s tr t ∧ abiPreserved s t ∧ (cbcX86_64 false).post s t := by
  have hp := UPre.of hs
  obtain ⟨tr,t,he,hq,hf⟩ := correct_wp hp
  refine ⟨tr,t,he,abiPreserved_of_exec (by decide +kernel) he
    ⟨fun r hr => Exec.gpr (keeps r hr) he,?_⟩,hq⟩
  exact hf.readW (r := ⟨s.gpr .rsp,8⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.ret_iv
    · exact hp.ret_data
    · exact hp.ret_scr.sub_right (Region.sub_prefix (by decide))) (by decide)

theorem ct : ConstantTime isa (cbcX86_64 false).pre (cbcX86_64 false).pub decrypt := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi,.rsi,.rdx,.rcx,.r8,.r9,.rsp])
    ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1,h2,h3,h4,h5,h6,h7⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem implies : (cbcX86_64 false).Implies (Proof.AesCbc.decryptRoundsContract X86_64.abi 8) := by
  sig_implies [Proof.AesCbc.decryptRoundsContract,Spec.Cbc.aesSig,cbcX86_64,modeX86_64,cbcMode,
    ciphOf,cbc,cts,X86_64.abi,X86_64.argRegs] [sat] using sat

theorem verified : Verified X86_64.target decrypt (Proof.AesCbc.decryptRoundsContract X86_64.abi 8) :=
  Verified.of_correct correct ct implies

theorem written (s : State) (tr : List Leak) (t : State)
    (hs : (Proof.AesCbc.decryptRoundsContract X86_64.abi 8).pre s) (he : Exec isa decrypt s tr t) :
    Sig.writtenWithin (X86_64.abi.withConsts []) Spec.Cbc.aesSig [("scratch",224)] s t := by
  have hp := UPre.of (implies.pre s hs)
  obtain ⟨tr',t',he',_,hf⟩ := correct_wp hp
  obtain ⟨-,rfl⟩ := Exec.det he he'
  simp [Sig.writtenWithin,X86_64.abi,X86_64.argRegs,Abi.withConsts,Spec.Cbc.aesSig,
    Sig.words,Sig.arrays,Param.words,ArgWord.bits]
  intro i hi hlo
  have hib : i < 2176 := by simpa [Elem.size] using hlo
  exact hf _ fun r hr hc => by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.iv_scr _ hc (Offset.contains_base _ (by omega) (by omega))
    · exact hp.data_scr _ hc (Offset.contains_base _ (by omega) (by omega))
    · change (S s + BitVec.ofNat 64 i - S s).toNat + 1 ≤ 224 at hc
      rw [Offset.add_sub_cancel_left,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)] at hc
      omega

end VG.Proof.AesCbc.X86_64.Vaes512Decrypt
