module

public import VerifiedGarbage.Proof.Gcm.RISCV64.Ghash
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Absorb
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Flush
import VerifiedGarbage.Proof.Gcm.Compose
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Run
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RISCV64.Inline
public import VerifiedGarbage.Proof.Gcm.Stream
public import VerifiedGarbage.Impl.AesGcm.RISCV64

/-!
# AES-GCM on RISCV64: absorbing the text (`textAbsorb`)

Untrusted: everything here is checked by Lean. As on ARMv7
(`Proof/AesGcm/Arm/TextAbsorb.lean`): `textAbsorb` absorbs the `len` bytes
(`r19`) at `data` (`r20`) into GHASH as text: before the first text
(`text_len`, `r23`, 0) it pads the additional data (of `aad_len` bytes,
`r22`) first (`firstFlush`), and it does nothing for no bytes
(`textAbsorb_ok`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.RISCV64

open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashInput zeros padLen)
open VG.Proof.Gcm (Absorbed)

/-- The regions `textAbsorb` writes. -/
abbrev taFrame (st w sp : Addr) : List Region :=
  [⟨st + BitVec.ofNat 64 16, 16⟩, ⟨st + BitVec.ofNat 64 32, 16⟩, ⟨w + BitVec.ofNat 64 96, 16⟩,
    ⟨w + BitVec.ofNat 64 512, 256⟩, below sp 2048]

/-- After `textAbsorb`, from `m₀`: GHASH has absorbed `x`. -/
structure TaOut (V : Reg → BitVec 64) (sp : Addr) (H : Block) (x₀ x : List Byte) (m₀ : Mem) (s : State) :
    Prop where
  env : Env V sp s
  hH : blockAt s.mem (V .s2 + BitVec.ofNat 64 240) = H
  abs : Absorbed m₀ (V .s1 + BitVec.ofNat 64 16) (V .s1 + BitVec.ofNat 64 32) H x₀ →
    Absorbed s.mem (V .s1 + BitVec.ofNat 64 16) (V .s1 + BitVec.ofNat 64 32) H x
  frame : Frame (taFrame (V .s1) (V .s0) sp) m₀ s.mem

theorem abs_taFrame {st w sp : Addr} {m m' : Mem} (h : Frame (absFrame st w 16 sp) m m') :
    Frame (taFrame st w sp) m m' :=
  h.mono fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp

theorem t_taFrame {st w sp : Addr} {m m' : Mem} (h : Frame (tFrame st w 16 sp) m m') :
    Frame (taFrame st w sp) m m' :=
  h.mono fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp

/-- Code never changes the permissions or the stack pointer. -/
theorem WP.with_rdwr {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q) :
    WP isa c s fun s' => Q s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  obtain ⟨t, s', e, q⟩ := h
  exact ⟨t, s', e, q, Exec.rdwr e⟩

/-- A frozen register, as the number it holds. -/
theorem Env.ofNat {V : Reg → BitVec 64} {sp : Addr} {s : State} (he : Env V sp s) {r : Reg} (hr : r ∈ frozen) :
    s.gpr r = BitVec.ofNat 64 (V r).toNat := by
  rw [he.fr r hr, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem textArgs_ok {s : State} :
    WP isa (.block textArgs) s fun s' =>
      s'.gpr .s4 = s.gpr .s9 ∧ s'.gpr .s5 = s.gpr .s8 ∧
      s'.gpr .s6 = BitVec.ofNat 64 ((s.gpr .s11).toNat % 16) ∧
      (∀ r, r ≠ .s4 → r ≠ .s5 → r ≠ .s6 → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
  have hand := and15 (s.gpr .s11)
  simp only [textArgs]
  crun [Int.reduceNatCast', mov, hand]
  exact ⟨fun r a b c => by simp [a, b, c], ⟨rfl, rfl, rfl, rfl⟩⟩

section
variable {V : Reg → BitVec 64} {sp : Addr} (L : Lay (V .s2) (V .s1) (V .s0))
include L

theorem textAbsorb_ok {s : State} {H : Block} {a ct : List Byte} (he : Env V sp s)
    (hH : blockAt s.mem (V .s2 + BitVec.ofNat 64 240) = H)
    (hd : DataOk (V .s1) (V .s0) s (V .s9) (V .s8).toNat)
    (ha : a.length % 16 = (V .s10).toNat % 16) (hP : (V .s11).toNat = ct.length) :
    WP isa textAbsorb s (TaOut V sp H (ghashInput a ct)
      (ghashInput a (ct ++ bytesAt s.mem (V .s9) (V .s8).toNat)) s.mem) := by
  have hn := (V .s8).isLt
  refine WP.ite _ (eval_zero (he.ofNat (r := .s8) (by decide)) hn) (fun ht => ?_) (fun hf' => ?_)
  · have h0 : (V .s8).toNat = 0 := by simpa using ht
    rw [h0]
    refine WP.block_nil ⟨he, hH, fun hab => ?_, Frame.refl _ _⟩
    simp only [bytesAt, List.range_zero, List.map_nil, List.append_nil]; exact hab
  have h0 : (V .s8).toNat ≠ 0 := by simpa using hf'
  -- the additional data padded, before the first text
  let x' := if ct = [] then a ++ zeros (padLen a.length) else ghashInput a ct
  have hx' : x'.length % 16 = ct.length % 16 := by
    by_cases hc : ct = []
    · subst hc; simp only [x', ite_true, List.length_append, Proof.Gcm.length_zeros, List.length_nil]
      exact Proof.Gcm.length_pad_mod _
    · simp only [x', hc, ite_false, Proof.Gcm.ghashInput_of_ne hc, List.length_append, Proof.Gcm.length_zeros]
      have := Proof.Gcm.length_pad_mod a.length; omega
  have hlt := Nat.mod_lt a.length (show 16 > 0 by decide)
  have mid : WP isa (.ite (.zero .s11) firstFlush (.block [])) s fun s₄ => Env V sp s₄ ∧
      blockAt s₄.mem (V .s2 + BitVec.ofNat 64 240) = H ∧
      (Absorbed s.mem (V .s1 + BitVec.ofNat 64 16) (V .s1 + BitVec.ofNat 64 32) H (ghashInput a ct) →
        Absorbed s₄.mem (V .s1 + BitVec.ofNat 64 16) (V .s1 + BitVec.ofNat 64 32) H x') ∧
      Frame (tFrame (V .s1) (V .s0) 16 sp) s.mem s₄.mem := by
    refine WP.ite _ (eval_zero (he.ofNat (r := .s11) (by decide)) (V .s11).isLt) (fun ht => ?_) (fun hf₂ => ?_)
    · have hc : ct = [] := List.eq_nil_of_length_eq_zero (by rw [← hP]; simpa using ht)
      have h22 := he.fr .s10 (by decide)
      have hand := and15 (V .s10)
      have h₃ : WP isa (.block [.logicImm .and .s6 .s10 15]) s fun s₃ =>
          s₃.gpr .s6 = BitVec.ofNat 64 (a.length % 16) ∧ (∀ r, r ≠ .s6 → s₃.gpr r = s.gpr r) ∧
            Keeps s s₃ := by
        crun [Int.reduceNatCast', h22, hand, ha]
        exact ⟨fun r a => by simp [a], ⟨rfl, rfl, rfl, rfl⟩⟩
      refine WP.seq (WP.mono h₃ fun s₃ ⟨h26, hg₃, hk₃⟩ => ?_)
      have he₃ := he.keep (fun r hr => hg₃ r (by revert r; decide)) hk₃.sp hk₃.rd hk₃.wr
      refine WP.mono (flush_ok L (yo := 16) (.inr rfl) (x := a) (H := H) ⟨he₃, by rw [hk₃.mem]; exact hH⟩ h26)
        fun s₄ hfl => ?_
      have hf₄ := hfl.frame
      rw [hk₃.mem] at hf₄
      refine ⟨hfl.env, hfl.hH, fun hab => ?_, hf₄⟩
      simp only [x', hc, ite_true]
      refine hfl.abs ?_
      rw [hk₃.mem]; subst hc; exact hab
    · have hc : ct ≠ [] := fun e => by subst e; simp only [List.length_nil] at hP; simp [hP] at hf₂
      refine WP.block_nil ⟨he, hH, fun hab => ?_, Frame.refl _ _⟩
      simp only [x', hc, ite_false]; exact hab
  refine WP.seq (WP.mono (WP.with_rdwr mid) fun s₄ ⟨⟨he₄, hH₄, hab₄, hf₄⟩, rd₄, wr₄, sp₄⟩ => ?_)
  -- the arguments of `absorb`
  have h20 := he₄.fr .s9 (by decide); have h19 := he₄.ofNat (r := .s8) (by decide)
  have h23 := he₄.fr .s11 (by decide)
  have hand := and15 (V .s11)
  have h₅ : WP isa (.block textArgs) s₄ fun s₅ =>
      s₅.gpr .s4 = V .s9 ∧ s₅.gpr .s5 = BitVec.ofNat 64 (V .s8).toNat ∧
      s₅.gpr .s6 = BitVec.ofNat 64 ((V .s11).toNat % 16) ∧
      (∀ r, r ≠ .s4 → r ≠ .s5 → r ≠ .s6 → s₅.gpr r = s₄.gpr r) ∧ Keeps s₄ s₅ := by
    simp only [textArgs]
    crun [Int.reduceNatCast', h20, h19, h23, hand, mov]
    exact ⟨fun r a b c => by simp [a, b, c], ⟨rfl, rfl, rfl, rfl⟩⟩
  refine WP.seq (WP.mono h₅ fun s₅ ⟨h24₅, h25₅, h26₅, hg₅, hk₅⟩ => ?_)
  have he₅ := he₄.keep (fun r hr => hg₅ r (by revert r; decide) (by revert r; decide) (by revert r; decide))
    hk₅.sp hk₅.rd hk₅.wr
  have hai : AbsIn V sp 16 H x' (V .s9) (V .s8).toNat s₅ :=
    ⟨he₅, h24₅, h25₅, by rw [h26₅, hx', hP], hd.of_eq (hk₅.rd.trans rd₄) (hk₅.wr.trans wr₄) (hk₅.sp.trans sp₄),
      by rw [hk₅.mem]; exact hH₄⟩
  refine WP.mono (absorb_ok L (.inr rfl) hai) fun s₆ ho => ?_
  have hdat : bytesAt s₅.mem (V .s9) (V .s8).toNat = bytesAt s.mem (V .s9) (V .s8).toNat := by
    rw [hk₅.mem]
    exact bytesAt_frame hf₄ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact hd.st.sub_right (Lay.stSub (by decide))
      · exact hd.w.sub_right (Lay.wSub (by decide))
      · exact hd.w.sub_right (Lay.wSub (by decide))
      · exact he.sp ▸ hd.sk) (by have := hd.lt; omega)
  have hne : bytesAt s.mem (V .s9) (V .s8).toNat ≠ [] := by
    intro e; have := congrArg List.length e; rw [length_bytesAt] at this; exact h0 (by simpa using this)
  refine ⟨ho.env, ?_, ?_, ?_⟩
  · rw [blockAt_frame ho.frame (ctx_absFrame L (.inr rfl) he.stk'), hk₅.mem, hH₄]
  · intro hab
    have := ho.abs (by rw [hk₅.mem]; exact hab₄ hab)
    rw [hdat] at this
    rw [Proof.Gcm.ghashInput_append _ _ _ hne]
    exact this
  · have f₆ := ho.frame
    rw [hk₅.mem] at f₆
    exact (t_taFrame hf₄).trans (abs_taFrame f₆)

end

end VG.Proof.AesGcm.RISCV64
