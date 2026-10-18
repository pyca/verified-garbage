module

public import VerifiedGarbage.Proof.Dsa.X86_64.WidthMask
import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.Bignum.X86_64.CTR2
import VerifiedGarbage.Spec.Dsa.SignVerify

/-! # Public selection of supported DSA modulus widths -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem widthCompare_ok {s : State} {value n : Nat}
    (hv : value < 2 ^ 64) (hn : n < 2 ^ 31) (hd : s.gpr .rdx = BitVec.ofNat 64 value) :
    WP isa (.block [.alu .cmp .rdx (.imm (BitVec.ofNat 32 n))]) s fun t =>
      t.zf = some (decide (value = n)) ∧ t.gpr .rdx = BitVec.ofNat 64 value ∧ t.mem = s.mem ∧ Keep [.rdx] s t := by
  refine WP.mono (WP.keep [.rdx] (Q := fun t =>
    t.zf = some (decide (value = n)) ∧ t.gpr .rdx = BitVec.ofNat 64 value ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨⟨hz, ht, hm⟩, hk⟩ => ⟨hz, ht, hm, hk⟩
  xrun [hd, sx_ofNat hn, ofNat_sub_beq hv (show n < 2 ^ 64 by omega)]

/-- Recover the saved p width and prepare the first public branch. -/
theorem readWidth_ok {s : State} {B : Addr} {Z p : Nat} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (hZ : 184 ≤ Z) (hp : p < 2 ^ 64)
    (hw : word s.mem B 176 = BitVec.ofNat 64 p) :
    WP isa (.block [.mov .rdx (.mem (hdr 22)), .alu .cmp .rdx (.imm 128)]) s fun t =>
      t.zf = some (decide (p = 128)) ∧ t.gpr .rdx = BitVec.ofNat 64 p ∧ t.mem = s.mem ∧ Keep [.rdx] s t := by
  refine WP.mono (WP.keep [.rdx] (Q := fun t =>
    t.zf = some (decide (p = 128)) ∧ t.gpr .rdx = BitVec.ofNat 64 p ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨⟨hz, ht, hm⟩, hk⟩ => ⟨hz, ht, hm, hk⟩
  xrun [State.ea, hdr, hdi, hdrOff, hw, hs.ld hZ,
    show BitVec.signExtend 64 (128 : BitVec 32) = BitVec.ofNat 64 128 from rfl,
    ofNat_sub_beq hp (show 128 < 2 ^ 64 by decide)]

theorem mask_union (a b : Bool) : mask a ||| mask b = mask (a || b) := by
  cases a <;> cases b <;> decide

/-- The 2048-bit modulus supports both 224- and 256-bit subgroups. -/
theorem widthEither_ok {s : State} {q : Nat} (hq : q < 2 ^ 64)
    (h8 : s.gpr .r8 = BitVec.ofNat 64 q) :
    WP isa (.block (Checks.widthMask 28 ++ ([.mov .r10 (.reg .rax)] : List Instr) ++ Checks.widthMask 32 ++
      ([.alu .or .rax (.reg .r10)] : List Instr))) s fun t =>
      t.gpr .rax = mask (decide (q = 28 ∨ q = 32)) ∧ t.mem = s.mem ∧ Keep [.rax, .r10] s t := by
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (widthMask_ok (by decide) hq h8) fun u ⟨hua, hum, hku⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r10] (Q := fun v => v.gpr .r10 = mask (decide (q = 28)) ∧ v.mem = u.mem)
    (by xrun [hua]) rfl) fun v ⟨⟨hv10, hvm⟩, hkv⟩ => ?_
  rw [WP.block_append_iff]
  have hv8 := ((hku.trans hkv).gpr (show Reg.r8 ∉ _ by decide)).trans h8
  refine WP.mono (widthMask_ok (by decide) hq hv8) fun z ⟨hza, hzm, hkz⟩ => ?_
  have hz10 := (hkz.gpr (show Reg.r10 ∉ [Reg.rax] by decide)).trans hv10
  refine WP.mono (WP.keep [.rax] (Q := fun t =>
    t.gpr .rax = mask (decide (q = 28 ∨ q = 32)) ∧ t.mem = z.mem) ?_ rfl)
    fun t ⟨⟨ht, htm⟩, hkt⟩ =>
      ⟨ht, htm.trans (hzm.trans (hvm.trans hum)), (((hku.trans hkv).trans hkz).trans hkt).mono (by decide)⟩
  xrun [hza, hz10, mask_union]
  rw [← Bool.decide_or]
  exact congrArg mask (decide_eq_decide.mpr or_comm)

/-- The legacy 160-bit subgroup extends the two FIPS 2048-bit cases. -/
theorem width2048_ok {s : State} {q : Nat} (hq : q < 2 ^ 64)
    (h8 : s.gpr .r8 = BitVec.ofNat 64 q) :
    WP isa (.block Checks.width2048) s fun t =>
      t.gpr .rax = mask (decide (q = 20 ∨ q = 28 ∨ q = 32)) ∧
      t.mem = s.mem ∧ Keep [.rax, .r10] s t := by
  unfold Checks.width2048
  rw [show Checks.widthMask 28 ++ ([.mov .r10 (.reg .rax)] : List Instr) ++ Checks.widthMask 32 ++
      ([.alu .or .rax (.reg .r10)] : List Instr) ++ ([.mov .r10 (.reg .rax)] : List Instr) ++ Checks.widthMask 20 ++
      ([.alu .or .rax (.reg .r10)] : List Instr) =
      (Checks.widthMask 28 ++ ([.mov .r10 (.reg .rax)] : List Instr) ++ Checks.widthMask 32 ++
        ([.alu .or .rax (.reg .r10)] : List Instr)) ++
      (([.mov .r10 (.reg .rax)] : List Instr) ++ Checks.widthMask 20 ++ ([.alu .or .rax (.reg .r10)] : List Instr)) by
        simp only [List.append_assoc]]
  rw [WP.block_append_iff]
  refine WP.mono (widthEither_ok hq h8) fun u ⟨hua, hum, hku⟩ => ?_
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (WP.keep [.r10] (Q := fun v =>
    v.gpr .r10 = mask (decide (q = 28 ∨ q = 32)) ∧ v.mem = u.mem)
    (by xrun [hua]) rfl) fun v ⟨⟨hvs, hvm⟩, hkv⟩ => ?_
  rw [WP.block_append_iff]
  have hv8 := ((hku.trans hkv).gpr (show Reg.r8 ∉ _ by decide)).trans h8
  refine WP.mono (widthMask_ok (by decide) hq hv8) fun z ⟨hza, hzm, hkz⟩ => ?_
  have hzs := (hkz.gpr (show Reg.r10 ∉ [Reg.rax] by decide)).trans hvs
  refine WP.mono (WP.keep [.rax] (Q := fun t =>
    t.gpr .rax = mask (decide (q = 20 ∨ q = 28 ∨ q = 32)) ∧ t.mem = z.mem) ?_ rfl)
    fun t ⟨⟨ht, htm⟩, hkt⟩ =>
      ⟨ht, htm.trans (hzm.trans (hvm.trans hum)),
        (((hku.trans hkv).trans hkz).trans hkt).mono (by decide)⟩
  xrun [hza, hzs, mask_union, ← Bool.decide_or]

abbrev widthChoice : Prog isa :=
  .ite .e (.block (Checks.widthMask 20))
    (.seq (.block [.alu .cmp .rdx (.imm 256)])
      (.ite .e
        (.block Checks.width2048)
        (.seq (.block [.alu .cmp .rdx (.imm 384)])
          (.ite .e (.block (Checks.widthMask 32)) (.block [.mov32 .rax (.imm 0)])))))

/-- The supported-width switch returns exactly the spec's (L,N) predicate. -/
theorem widthChoice_ok {s : State} {p q : Nat} (hp : p < 2 ^ 64) (hq : q < 2 ^ 64)
    (hd : s.gpr .rdx = BitVec.ofNat 64 p) (h8 : s.gpr .r8 = BitVec.ofNat 64 q)
    (hz : s.zf = some (decide (p = 128))) :
    WP isa widthChoice s fun t =>
      t.gpr .rax = mask (decide (Spec.Dsa.supportedSizes (8 * p) (8 * q))) ∧
      t.mem = s.mem ∧ Keep [.rax, .rdx, .r10] s t := by
  unfold widthChoice
  by_cases h128 : p = 128
  · refine WP.ite true ?_ (fun _ => ?_) (fun h => Bool.noConfusion h)
    · change VG.X86_64.eval .e s = some true
      simp only [VG.X86_64.eval, hz, h128, decide_true]
    · have he : Spec.Dsa.supportedSizes (8 * p) (8 * q) ↔ q = 20 := by
        unfold Spec.Dsa.supportedSizes; omega
      rw [decide_eq_decide.mpr he]
      exact WP.mono (widthMask_ok (by decide) hq h8) fun t ⟨ht, hm, hk⟩ => ⟨ht, hm, hk.mono (by decide)⟩
  · refine WP.ite false ?_ (fun h => Bool.noConfusion h) (fun _ => ?_)
    · change VG.X86_64.eval .e s = some false
      simp only [VG.X86_64.eval, hz, h128, decide_false]
    · refine WP.seq (WP.mono (widthCompare_ok hp (show 256 < 2 ^ 31 by decide) hd)
        fun u ⟨huz, hud, hum, hku⟩ => ?_)
      have hu8 := (hku.gpr (show Reg.r8 ∉ [Reg.rdx] by decide)).trans h8
      by_cases h256 : p = 256
      · refine WP.ite true ?_ (fun _ => ?_) (fun h => Bool.noConfusion h)
        · change VG.X86_64.eval .e u = some true
          simp only [VG.X86_64.eval, huz, h256, decide_true]
        · have he : Spec.Dsa.supportedSizes (8 * p) (8 * q) ↔ q = 20 ∨ q = 28 ∨ q = 32 := by
            unfold Spec.Dsa.supportedSizes; omega
          rw [decide_eq_decide.mpr he]
          exact WP.mono (width2048_ok hq hu8) fun t ⟨ht, hm, hk⟩ =>
            ⟨ht, hm.trans hum, (hku.trans hk).mono (by decide)⟩
      · refine WP.ite false ?_ (fun h => Bool.noConfusion h) (fun _ => ?_)
        · change VG.X86_64.eval .e u = some false
          simp only [VG.X86_64.eval, huz, h256, decide_false]
        · refine WP.seq (WP.mono (widthCompare_ok hp (show 384 < 2 ^ 31 by decide) hud)
            fun v ⟨hvz, _, hvm, hkv⟩ => ?_)
          have hv8 := (hkv.gpr (show Reg.r8 ∉ [Reg.rdx] by decide)).trans hu8
          by_cases h384 : p = 384
          · refine WP.ite true ?_ (fun _ => ?_) (fun h => Bool.noConfusion h)
            · change VG.X86_64.eval .e v = some true
              simp only [VG.X86_64.eval, hvz, h384, decide_true]
            · have he : Spec.Dsa.supportedSizes (8 * p) (8 * q) ↔ q = 32 := by
                unfold Spec.Dsa.supportedSizes; omega
              rw [decide_eq_decide.mpr he]
              exact WP.mono (widthMask_ok (by decide) hq hv8) fun t ⟨ht, hm, hk⟩ =>
                ⟨ht, hm.trans (hvm.trans hum), ((hku.trans hkv).trans hk).mono (by decide)⟩
          · refine WP.ite false ?_ (fun h => Bool.noConfusion h) (fun _ => ?_)
            · change VG.X86_64.eval .e v = some false
              simp only [VG.X86_64.eval, hvz, h384, decide_false]
            · have he : ¬ Spec.Dsa.supportedSizes (8 * p) (8 * q) := by
                unfold Spec.Dsa.supportedSizes; omega
              rw [decide_eq_false he]
              refine WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = mask false ∧ t.mem = v.mem)
                (by xrun) rfl) fun t ⟨⟨ht, hm⟩, hk⟩ =>
                  ⟨ht, hm.trans (hvm.trans hum), ((hku.trans hkv).trans hk).mono (by decide)⟩

end VG.Proof.Dsa.X86_64
