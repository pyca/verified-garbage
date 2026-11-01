module

public import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.Tag
public import VerifiedGarbage.Proof.AesGcm.RISCV64.FinTag
public import VerifiedGarbage.Proof.Gcm.Compose
import VerifiedGarbage.Proof.AesGcm.RISCV64.Absorb
import VerifiedGarbage.Proof.AesGcm.RISCV64.Flush
import VerifiedGarbage.Proof.AesGcm.RISCV64.TextAbsorb
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Run
import VerifiedGarbage.Proof.Framework.Offset

/-!
# SM4-GCM on RISC-V: the tag after the last piece (`finTag o`)

Untrusted: everything here is checked by Lean. AES-GCM's `finTag o`
(`Proof/AesGcm/RISCV64/FinTag.lean`) with SM4's `tag o`: it pads and absorbs
the buffered bytes (`flush`), then puts the tag into `W + o` (`finTag_ok`).
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.RISCV64

open VG VG.RISCV64 VG.Impl.Sm4Gcm.RISCV64
open VG.Impl.AesGcm.RISCV64 (mov flush)
open VG.Proof.AesGcm.RISCV64 hiding CrIn CrMid CrOut crFrame ciphOf TailKs ctx_crFrame ciph_frame
  CtrCall CtrPost ctr_call ctr_rel tagFrame TagOut TagMid tagLens_ok tagArgs_ok ctrTag_mk tagCall_ok
  tag_ok tFrame_sub t_tagFrame FinOut finTag_ok
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashInput ghash ghashFrom blocks zeros padLen toBytes ofBytes)
open VG.Proof.Gcm (Absorbed lensBlock padded)

/-- `tFrame` is within `tagFrame`. -/
theorem tFrame_sub {st w sp : Addr} {o : Nat} :
    ∀ r ∈ tFrame st w 16 sp, ∃ r' ∈ tagFrame st w o sp, Region.Sub r r' := fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self .., by simpa using Offset.sub_base st (show 16 + 16 ≤ 32 by decide)⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
  · exact ⟨⟨w + BitVec.ofNat 64 512, 256⟩, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, below_sub⟩

theorem t_tagFrame {st w sp : Addr} {o : Nat} {m m' : Mem} (h : Frame (tFrame st w 16 sp) m m') :
    Frame (tagFrame st w o sp) m m' := h.sub tFrame_sub

/-- After `finTag o`, from `m₀`. -/
structure FinOut (V : Reg → BitVec 64) (sp : Addr) (o : Nat) (H : Block) (a ct : List Byte) (m₀ : Mem)
    (s : State) : Prop where
  env : Env V sp s
  out : Absorbed m₀ (V .s1 + BitVec.ofNat 64 16) (V .s1 + BitVec.ofNat 64 32) H (ghashInput a ct) →
    bytesAt s.mem (V .s0 + BitVec.ofNat 64 o) 16 =
      toBytes (ghashFrom H (ghash H (blocks (padded a ct))) [ofBytes (lensBlock (V .s10).toNat ct.length)]
        ^^^ ciphOf m₀ (V .s2) (blockAt m₀ (V .s1)))
  frame : Frame (tagFrame (V .s1) (V .s0) o sp) m₀ s.mem

section
variable {V : Reg → BitVec 64} {sp : Addr} (L : Lay (V .s2) (V .s1) (V .s0))
include L

theorem finTag_ok (hb : Big V sp) {o : Nat} (ho : o = 0 ∨ o = 112) {H : Block} {a ct : List Byte}
    {s : State} (he : Env V sp s)
    (hH : blockAt s.mem (V .s2 + BitVec.ofNat 64 240) = H)
    (ha : a.length % 16 = (V .s10).toNat % 16) (hP : (V .s11).toNat = ct.length) :
    WP isa (finTag o) s (FinOut V sp o H a ct s.mem) := by
  have h22 := he.fr .s10 (by decide)
  have h23 := he.fr .s11 (by decide)
  -- `s6`: the length of the buffered bytes, modulo 16
  have mid : WP isa (.ite (.zero .s11) (.block [.logicImm .and .s6 .s10 15])
      (.block [.logicImm .and .s6 .s11 15])) s fun s₂ =>
      s₂.gpr .s6 = BitVec.ofNat 64 ((ghashInput a ct).length % 16) ∧
        (∀ r, r ≠ .s6 → s₂.gpr r = s.gpr r) ∧ Keeps s s₂ := by
    refine WP.ite _ (eval_zero (he.ofNat (r := .s11) (by decide)) (V .s11).isLt) (fun ht => ?_) (fun hf => ?_)
    · have hc : ct = [] := List.eq_nil_of_length_eq_zero (by rw [← hP]; simpa using ht)
      have e : (ghashInput a ct).length % 16 = (V .s10).toNat % 16 := by
        rw [hc, Proof.Gcm.ghashInput_nil, ha]
      have hand := and15 (V .s10)
      rw [e]
      crun [Int.reduceNatCast', h22, hand]
      exact ⟨fun r a => by simp [a], ⟨rfl, rfl, rfl, rfl⟩⟩
    · have hc : ct ≠ [] := fun e => by subst e; simp only [List.length_nil] at hP; simp [hP] at hf
      have e : (ghashInput a ct).length % 16 = (V .s11).toNat % 16 := by
        rw [Proof.Gcm.ghashInput_of_ne hc, List.length_append, List.length_append, Proof.Gcm.length_zeros, hP]
        have := Proof.Gcm.length_pad_mod a.length; omega
      have hand := and15 (V .s11)
      rw [e]
      crun [Int.reduceNatCast', h23, hand]
      exact ⟨fun r a => by simp [a], ⟨rfl, rfl, rfl, rfl⟩⟩
  refine WP.seq (WP.mono mid fun s₂ ⟨h26₂, hg₂, hk₂⟩ => ?_)
  have he₂ := he.keep (fun r hr => hg₂ r (by revert r; decide)) hk₂.sp hk₂.rd hk₂.wr
  refine WP.seq (WP.mono (flush_ok L (yo := 16) (.inr rfl) (x := ghashInput a ct) (H := H)
    ⟨he₂, by rw [hk₂.mem]; exact hH⟩ h26₂) fun s₄ hfl => ?_)
  have hf₄ := hfl.frame
  rw [hk₂.mem] at hf₄
  -- the lengths
  have h₅ : WP isa (.block [mov .s4 .s10, mov .s6 .s11]) s₄ fun s₅ =>
      s₅.gpr .s4 = V .s10 ∧ s₅.gpr .s6 = V .s11 ∧ (∀ r, r ≠ .s4 → r ≠ .s6 → s₅.gpr r = s₄.gpr r) ∧
        Keeps s₄ s₅ := by
    have e22 := hfl.env.fr .s10 (by decide)
    have e23 := hfl.env.fr .s11 (by decide)
    crun [Int.reduceNatCast', mov, e22, e23]
    exact ⟨fun r a b => by simp [a, b], ⟨rfl, rfl, rfl, rfl⟩⟩
  refine WP.seq (WP.mono h₅ fun s₅ ⟨h24₅, h26₅, hg₅, hk₅⟩ => ?_)
  have he₅ := hfl.env.keep (fun r hr => hg₅ r (by revert r; decide) (by revert r; decide)) hk₅.sp hk₅.rd hk₅.wr
  refine WP.mono (tag_ok L hb ho he₅ (H := H) (by rw [hk₅.mem]; exact hfl.hH) rfl) fun s₆ tg => ?_
  rw [h24₅, h26₅, hP, hk₅.mem] at tg
  refine ⟨tg.env, fun hab => ?_, (t_tagFrame hf₄).trans tg.frame⟩
  rw [tg.out]
  have hw := (hfl.abs (by rw [hk₂.mem]; exact hab)).whole_eq (by
    simp only [List.length_append, Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod _)
  rw [show ghashInput a ct ++ zeros (padLen (ghashInput a ct).length) = padded a ct from rfl] at hw
  rw [hw, ciph_frame hf₄ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact L.cs.sub_right (Lay.stSub (by decide))
      · exact L.cw'.sub_right (Lay.wSub (by decide))
      · exact L.cw'.sub_right (Lay.wSub (by decide))
      · exact he.stk'.c),
    blockAt_frame hf₄ (j_tFrame L he.stk')]

end

end VG.Proof.Sm4Gcm.RISCV64
