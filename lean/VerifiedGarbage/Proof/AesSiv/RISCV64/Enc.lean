module

public import VerifiedGarbage.Proof.AesSiv.RISCV64.Short
import VerifiedGarbage.Proof.AesSiv.RISCV64.Long
public import VerifiedGarbage.Proof.AesSiv.RISCV64.CtrLoop
import VerifiedGarbage.Proof.AesSiv.RISCV64.Fn
public import VerifiedGarbage.Spec.Siv.Contract
import VerifiedGarbage.Proof.AesSiv.Scratch
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.AesSiv.RISCV64
public import VerifiedGarbage.Proof.AesSiv.RISCV64.Env
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill

/-! ### `AesSiv.RISCV64.Entry`, which this module and modules that import it used -/

section

/-!
# AES-SIV on RISC-V: the arguments, the entry and the exit

Untrusted: everything here is checked by Lean. `encrypt` and `decrypt` are
given their public values in `a0`–`a7` (`Args`). `entry` saves our caller's
registers and the return address at `W + 128` and keeps the arguments in
`s1`–`s5` and `s9`–`s11` (`entry_wp`); `restore` reloads them, `s1`, the
base, last (`exit_wp`). The pieces write only the parts of `W` in `mutR`
and the data, so the slots stay as the entry left them. As on PPC64LE
(`Proof/AesSiv/PPC64LE/Entry.lean`); the entry saves every callee-saved
register, so none is left for the pieces to keep untouched.
-/

@[expose] public section

namespace VG.Proof.AesSiv.RISCV64

open VG VG.Impl.AesSiv.RISCV64
open VG.RISCV64 VG.RISCV64.Steps
open VG.RISCV64.Spill (saveCode saveMem Saved saveMem_saved save_ok restoreCode restore_wp)

/-- What `encrypt` and `decrypt` are given: the public values `c`. -/
structure Args (c : Cx) (s : State) : Prop where
  lay : Lay c
  a0 : s.gpr .a0 = c.C
  a1 : s.gpr .a1 = BitVec.ofNat 64 c.R
  a2 : s.gpr .a2 = c.A
  a3 : s.gpr .a3 = BitVec.ofNat 64 c.N
  a4 : s.gpr .a4 = c.D
  a5 : s.gpr .a5 = BitVec.ofNat 64 c.n
  a6 : s.gpr .a6 = c.V
  a7 : s.gpr .a7 = c.W
  perm : Perm c s

/-! ## What the pieces write -/

/-- What the pieces write: the parts of `W` below the slots and above them,
and the data. -/
abbrev mutR (c : Cx) : List Region := [⟨c.W, 128⟩, ⟨c.W + BitVec.ofNat 64 240, 2336⟩, ⟨c.D, c.n⟩]

theorem sub_lo {c : Cx} {d k : Nat} (h : d + k ≤ 128) :
    ∃ r' ∈ mutR c, Region.Sub ⟨c.W + BitVec.ofNat 64 d, k⟩ r' :=
  ⟨⟨c.W, 128⟩, by simp, Offset.sub_base _ h⟩

theorem sub_hi {c : Cx} {d k : Nat} (h₁ : 240 ≤ d) (h₂ : d + k ≤ 2576) :
    ∃ r' ∈ mutR c, Region.Sub ⟨c.W + BitVec.ofNat 64 d, k⟩ r' :=
  ⟨⟨c.W + BitVec.ofNat 64 240, 2336⟩, by simp, Offset.sub _ h₁ (by omega_using [h₂])⟩

theorem sub_data {c : Cx} : ∃ r' ∈ mutR c, Region.Sub ⟨c.D, c.n⟩ r' := ⟨_, by simp, fun _ h => h⟩

/-! ## The entry -/

/-- What the entry writes: the saved registers and the return address. -/
abbrev entryR (W : Addr) : Region := ⟨W + BitVec.ofNat 64 128, 104⟩

/-- The slots of our caller's registers and of the return address, in the
order the entry saves them. -/
abbrev savedL : List (Reg × Nat) := saved ++ [(.ra, raO)]

theorem savedL_bound : ∀ p ∈ savedL, 128 ≤ p.2 ∧ p.2 + 8 ≤ 128 + 104 := by decide

theorem savedL_fits : Spill.Fits savedL := by decide

theorem savedL_off : ∀ p ∈ savedL, p.2 % 8 = 0 ∧ p.2 < 2048 := by decide

/-- The slots are kept by what the pieces write. -/
theorem slots_mut {c : Cx} (L : Lay c) : ∀ r ∈ mutR c, (entryR c.W).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (Lay.w0_w (c := c) (n := 128) (d := 128) (k := 104) (Nat.le_refl _) (by decide)).symm
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.d_w' (by decide)).symm

/-- Our caller's registers, kept in their slots by writes to `mutR`. -/
theorem saved_mut {c : Cx} (L : Lay c) {g : Reg → BitVec 64} {m m' : Mem} (hf : Frame (mutR c) m m')
    (h : Saved c.W g savedL m) : Saved c.W g savedL m' :=
  h.frame_in savedL_bound hf (slots_mut L)

/-- What the entry leaves. -/
structure Entered (c : Cx) (s s₁ : State) : Prop where
  env : Env c s₁
  s4 : s₁.gpr .s4 = c.A
  s5 : s₁.gpr .s5 = BitVec.ofNat 64 c.N
  saved : Saved c.W s.gpr savedL s₁.mem
  frame : Frame [entryR c.W] s.mem s₁.mem
  rd : s₁.rd = s.rd
  wr : s₁.wr = s.wr
  sp : s₁.sp = s.sp

theorem entry_code : entry = saveCode .a7 savedL ++
    ([Impl.AesCbc.RISCV64.mov .s1 .a7, Impl.AesCbc.RISCV64.mov .s2 .a0, Impl.AesCbc.RISCV64.mov .s3 .a1,
      Impl.AesCbc.RISCV64.mov .s4 .a2, Impl.AesCbc.RISCV64.mov .s5 .a3, Impl.AesCbc.RISCV64.mov .s9 .a4,
      Impl.AesCbc.RISCV64.mov .s10 .a5, Impl.AesCbc.RISCV64.mov .s11 .a6] : List Instr) := rfl

theorem entry_wp {c : Cx} {s : State} (Ar : Args c s) : WP isa (.block entry) s (Entered c s) := by
  have L := Ar.lay
  have hww := L.ww
  rw [entry_code]
  refine save_ok (b := .a7) (by rw [Ar.a7]; exact L.wal) savedL_off (fun p hp => by
    rw [Ar.a7]; exact Ar.perm.wW (by have := savedL_bound p hp; omega_using [this])) ?_
  rw [Ar.a7]
  generalize hs₀ : ({ s with mem := saveMem s.mem c.W s.gpr savedL } : State) = s₀
  have g₀ : s₀.gpr = s.gpr := by rw [← hs₀]
  have rd₀ : s₀.rd = s.rd := by rw [← hs₀]
  have wr₀ : s₀.wr = s.wr := by rw [← hs₀]
  have sp₀ : s₀.sp = s.sp := by rw [← hs₀]
  have m₀ : s₀.mem = saveMem s.mem c.W s.gpr savedL := by rw [← hs₀]
  refine wp_mv fun s₁ u₁ => wp_mv fun s₂ u₂ => wp_mv fun s₃ u₃ => wp_mv fun s₄ u₄ => wp_mv fun s₅ u₅ =>
    wp_mv fun s₆ u₆ => wp_mv fun s₇ u₇ => wp_mv fun s₈ u₈ => WP.block_nil ?_
  have m₈ : s₈.mem = s₀.mem := by
    rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have rd₈ : s₈.rd = s.rd := by
    rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, rd₀]
  have wr₈ : s₈.wr = s.wr := by
    rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, wr₀]
  -- Each move reads an argument register, which no earlier move writes.
  have g : ∀ r, r ∉ [Reg.s1, .s2, .s3, .s4, .s5, .s9, .s10, .s11] → s₈.gpr r = s.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h2, h3, h4, h5, h9, h10, h11⟩ := hr
    rw [u₈.other _ h11, u₇.other _ h10, u₆.other _ h9, u₅.other _ h5, u₄.other _ h4, u₃.other _ h3,
      u₂.other _ h2, u₁.other _ h1, g₀]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, Ar.perm.of_eq rd₈ wr₈⟩, ?_, ?_, ?_, ?_, rd₈, wr₈, ?_⟩
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, g₀, Ar.a7]
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), g₀, Ar.a0]
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), g₀, Ar.a1]
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), g₀,
      Ar.a4]
  · rw [u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), g₀,
      Ar.a5]
  · rw [u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), g₀,
      Ar.a6]
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), g₀, Ar.a2]
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr,
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), g₀,
      Ar.a3]
  · rw [m₈, m₀]; exact saveMem_saved savedL_fits _ _ _
  · rw [m₈, m₀]; exact Spill.saveMem_frame savedL_bound (by omega_using []) _ _ _
  · rw [u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, sp₀]

/-! ## The exit -/

/-- The slots `restore` reloads, in its order. -/
abbrev restoreL : List (Reg × Nat) := (.ra, raO) :: saved

theorem restore_code : restore = restoreCode .s1 restoreL := rfl

theorem restoreL_sub : ∀ p ∈ restoreL, p ∈ savedL := by decide

theorem preserved_restored : ∀ r ∈ preserved, r ∈ restoreL.map Prod.fst := by decide

/-- `restore`: our caller's registers and return address back, for `s₀` the
state at the entry. -/
theorem exit_wp {c : Cx} (L : Lay c) {s₀ s : State} (E : Env c s) (sv : Saved c.W s₀.gpr savedL s.mem)
    (hsp : s.sp = s₀.sp) :
    WP isa (.block restore) s fun s' => abiPreserved s₀ s' ∧ s'.mem = s.mem ∧ s'.gpr .a0 = s.gpr .a0 := by
  rw [restore_code]
  refine WP.mono (restore_wp (b := .s1) (B := c.W) L.wal E.s1 (by decide) (by decide) (fun p hp => by
      have := savedL_bound p (restoreL_sub p hp)
      exact E.perm.wR (by omega_using [this])) (sv.sub restoreL_sub)) fun s' R => ?_
  refine ⟨⟨fun r hr => ?_, by rw [R.sp, hsp], R.gpr (.ra, raO) List.mem_cons_self⟩, R.mem,
    R.other _ (by decide)⟩
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (preserved_restored r hr)
  exact R.gpr p hp

end VG.Proof.AesSiv.RISCV64

end

end

/-!
# AES-SIV on RISC-V: `encrypt`

Untrusted: everything here is checked by Lean. `encS2v` saves our caller's
registers, computes S2V's first state and S2V of the associated data
(`encS2v_wp`); `encrypt` then finishes S2V with the plaintext into `W`, which
is the synthetic IV `V`, encrypts the plaintext in place by CTR from `V`'s
counter, copies `V` to `siv` and restores our caller's registers
(`encrypt_wp`). Everything but the data and `siv` that the code writes is in
`W`, which the key context, the descriptors and the components miss
(`WF`). As on PPC64LE (`Proof/AesSiv/PPC64LE/Enc.lean`).
-/

@[expose] public section

namespace VG.Proof.AesSiv.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.AesSiv.RISCV64
open VG.Spec.Aes (bytesAt)

/-! ## Writes within `W` -/

/-- A frame within `W`. -/
abbrev WF (c : Cx) (m m' : Mem) : Prop := Frame [⟨c.W, 2576⟩] m m'

theorem WF.of {c : Cx} {rs : List Region} {m m' : Mem} (h : Frame rs m m')
    (hs : ∀ r ∈ rs, Region.Sub r ⟨c.W, 2576⟩) : WF c m m' :=
  h.sub fun r hr => ⟨_, List.mem_singleton_self _, hs r hr⟩

theorem WF.trans {c : Cx} {m₁ m₂ m₃ : Mem} (h₁ : WF c m₁ m₂) (h₂ : WF c m₂ m₃) : WF c m₁ m₃ :=
  Frame.trans h₁ h₂

theorem wR_sub {c : Cx} : ∀ r ∈ wR c, Region.Sub r ⟨c.W, 2576⟩ := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> exact Lay.wSub (by decide)

theorem oR_sub {c : Cx} {out : Nat} (h : out + 16 ≤ 2576) : ∀ r ∈ oR c out, Region.Sub r ⟨c.W, 2576⟩ := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · exact Lay.wSub h
  · exact wR_sub r hr

theorem WF.ctxMac {c : Cx} (L : Lay c) {m m' : Mem} (h : WF c m m') :
    Spec.Siv.ctxMac m' c.C c.R = Spec.Siv.ctxMac m c.C c.R :=
  ctxMac_frame h (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact L.c_w) L.rb

theorem WF.ctxCiph {c : Cx} (L : Lay c) {m m' : Mem} (h : WF c m m') :
    Spec.Siv.ctxCiph m' c.C c.R = Spec.Siv.ctxCiph m c.C c.R :=
  ctxCiph_frame h (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact L.c_w) L.rb

theorem WF.data {c : Cx} (L : Lay c) {m m' : Mem} (h : WF c m m') : bytesAt m' c.D c.n = bytesAt m c.D c.n :=
  Proof.Cmac.bytesAt_frame h (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact L.d_w) (by have := L.n_lt; omega_using [this])

theorem WF.descW {c : Cx} (L : Lay c) {m m' : Mem} (h : WF c m m') {i j : Nat} (hi : i < c.N) (hj : j < 2) :
    descW m' c.A i j = descW m c.A i j := by
  have aw := L.aw
  exact h.readW (r := ⟨c.A + BitVec.ofNat 64 (16 * i + 8 * j), 8⟩) (Region.contains_self _ _)
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact L.a_w.sub_left (Offset.sub_base _ (by omega_using [hi, hj]))) (by decide)

theorem WF.ads {c : Cx} (L : Lay c) {m m' : Mem} (h : WF c m m') {s : State} (hA : Ads c m s) : Ads c m' s :=
  fun i hi => by rw [h.descW L hi (by decide), h.descW L hi (by decide)]; exact hA i hi

/-- The `i`-th region the descriptors list. -/
theorem listed_eq (m : Mem) (A : Addr) (i : Nat) :
    (⟨(m.readW (A + BitVec.ofNat 64 (i * (2 * (64 / 8)))) 64).setWidth 64,
      (m.readW (A + BitVec.ofNat 64 (i * (2 * (64 / 8))) + BitVec.ofNat 64 (64 / 8)) 64).toNat * Elem.size .u8⟩ :
        Region) = ⟨descW m A i 0, (descW m A i 1).toNat⟩ := by
  simp only [descW, BitVec.setWidth_eq, Elem.size, Nat.mul_one]
  rw [show i * (2 * (64 / 8)) = 16 * i + 8 * 0 by omega_using [], show (64 / 8 : Nat) = 8 from rfl, Offset.add_add,
    show 16 * i + 8 * 0 + 8 = 16 * i + 8 * 1 by omega_using []]

theorem WF.components {c : Cx} (L : Lay c) {m m' : Mem} (h : WF c m m') {s : State} (hA : Ads c m s) :
    Spec.Siv.components 64 m' c.A c.N = Spec.Siv.components 64 m c.A c.N := by
  refine Proof.AesSiv.components_congr fun r hr a ha => (h a fun r' hr' hc => ?_).symm
  simp only [List.mem_singleton] at hr'; subst hr'
  rcases List.mem_cons.mp hr with rfl | hr
  · refine L.a_w a ?_ hc
    simp only [Sig.descRegion, Region.Contains] at ha ⊢
    omega_using [ha]
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
    have hb := (hA i (List.mem_range.mp hi)).w
    rw [listed_eq] at ha
    exact hb a ha hc

/-! ## S2V of the associated data -/

/-- What S2V of the associated data leaves, from the state `σ` at the entry
and the state `s₁` after it. -/
structure S2vDone (c : Cx) (σ s₁ s : State) : Prop where
  en : Entered c σ s₁
  inv : AInv c s₁ c.N s

theorem encS2v_wp {c : Cx} {s : State} (Ar : Args c s) (hA : Ads c s.mem s) {rest : Prog isa} {Q : State → Prop}
    (k : ∀ s₁ s', S2vDone c s s₁ s' → s'.gpr .s6 = c.D → s'.gpr .s7 = BitVec.ofNat 64 c.n → WP isa rest s' Q) :
    WP isa (.seq encS2v rest) s Q := by
  have L := Ar.lay
  unfold encS2v
  refine WP.seq (WP.seq (WP.block_append_iff.mpr (WP.mono (entry_wp Ar) fun s₁ En => ?_)))
  have E₁ := En.env
  refine WP.mono (WP.seq_iff.mp (start_wp L E₁)) fun s₂' h => WP.seq (WP.mono h fun s₂ ⟨K₂, f₂, d₂⟩ => ?_)
  have wf₁ : WF c s.mem s₁.mem := WF.of En.frame fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact Lay.wSub (by decide)
  have I₀ : AInv c s₁ 0 s₂ :=
    { env := E₁.of_pk K₂.pk
      pk := K₂.pk
      ads := (wf₁.ads L hA).of_eq (by rw [K₂.pk.rd, En.rd]) (by rw [K₂.pk.wr, En.wr])
      s4 := by rw [K₂.s4, En.s4, Nat.mul_zero, BitVec.add_zero]
      s5 := by rw [K₂.s5, En.s5, Nat.sub_zero]
      frame := f₂
      acc := by rw [d₂, List.take_zero, Spec.Siv.s2vAcc, List.foldl_nil] }
  refine WP.seq (WP.mono (s2vAds_wp L I₀) fun s₃ I₃ => ?_)
  refine wp_mv fun s₄ u₄ => wp_mv fun s₅ u₅ => WP.block_nil ?_
  have pk₅ : PK s₃ s₅ := (PK.ofUpd u₄).trans (PK.ofUpd u₅)
  refine k s₁ s₅ ⟨En, ⟨I₃.env.of_pk pk₅, I₃.pk.trans pk₅, I₃.ads.of_eq pk₅.rd pk₅.wr,
      by rw [u₅.other _ (by decide), u₄.other _ (by decide), I₃.s4],
      by rw [u₅.other _ (by decide), u₄.other _ (by decide), I₃.s5],
      by rw [u₅.mem, u₄.mem]; exact I₃.frame, by rw [u₅.mem, u₄.mem]; exact I₃.acc⟩⟩
    (by rw [u₅.other _ (by decide), u₄.gpr, I₃.env.s9])
    (by rw [u₅.gpr, u₄.other _ (by decide), I₃.env.s10])

/-- The facts of `S2vDone` about the entry's memory. -/
theorem S2vDone.facts {c : Cx} (L : Lay c) {σ s₁ s : State} (h : S2vDone c σ s₁ s) (hA : Ads c σ.mem σ) :
    WF c σ.mem s.mem ∧ bytesAt s.mem (c.W + BitVec.ofNat 64 dO) 16 =
      Spec.Siv.s2vAcc (Spec.Siv.ctxMac σ.mem c.C c.R) (Spec.Siv.components 64 σ.mem c.A c.N) := by
  have wf₁ : WF c σ.mem s₁.mem := WF.of h.en.frame fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact Lay.wSub (by decide)
  refine ⟨wf₁.trans (WF.of h.inv.frame wR_sub), ?_⟩
  rw [h.inv.acc, List.take_of_length_le (by rw [length_components]), wf₁.ctxMac L, wf₁.components L hA]

/-! ## `encrypt` -/

theorem mutR_wR {c : Cx} : ∀ r ∈ wR c, ∃ r' ∈ mutR c, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact sub_lo (by decide)
  · exact sub_hi (by decide) (by decide)

theorem mutR_oR {c : Cx} {out : Nat} (h : out + 16 ≤ 128) : ∀ r ∈ oR c out, ∃ r' ∈ mutR c, Region.Sub r r' := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · exact sub_lo h
  · exact mutR_wR r hr

theorem mutR_ctrR {c : Cx} : ∀ r ∈ ctrR c, ∃ r' ∈ mutR c, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact sub_data
  · exact sub_lo (by decide)
  · exact sub_hi (by decide) (by decide)

theorem ctrR_W0 {c : Cx} (L : Lay c) :
    ∀ r ∈ ctrR c, (⟨c.W + BitVec.ofNat 64 0, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (L.d_w' (by decide)).symm
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)

/-- `vg_aes_siv_encrypt`: `encryptWith`'s synthetic IV at `siv` and ciphertext
at `data`. -/
theorem encrypt_wp {c : Cx} {s : State} (Ar : Args c s) (hA : Ads c s.mem s) (hV : Covers [⟨c.V, 16⟩] s.wr) :
    WP isa encrypt s fun s' => abiPreserved s s' ∧
      Spec.Siv.encryptWith (Spec.Siv.ctxMac s.mem c.C c.R) (Spec.Siv.ctxCiph s.mem c.C c.R)
          (Spec.Siv.components 64 s.mem c.A c.N) (bytesAt s.mem c.D c.n) =
        (bytesAt s'.mem c.V 16, bytesAt s'.mem c.D c.n) := by
  have L := Ar.lay
  unfold encrypt
  refine encS2v_wp Ar hA fun s₁ s₄ S h6 h7 => ?_
  obtain ⟨wf₄, acc₄⟩ := S.facts L hA
  have E₄ := S.inv.env
  refine WP.seq (WP.mono (finish_wp L E₄ (L.bufD E₄.perm) h6 h7 (out := 0) (.inl rfl))
    fun s₅ ⟨pk₅, f₅, v₅⟩ => ?_)
  have E₅ := E₄.of_pk pk₅
  have wf₅ : WF c s.mem s₅.mem := wf₄.trans (WF.of f₅ (oR_sub (by decide)))
  refine WP.seq (WP.mono (ctr_wp L E₅ (src := 0) (by decide) (by decide)) fun s₆ ⟨pk₆, f₆, d₆⟩ => ?_)
  have E₆ := E₅.of_pk pk₆
  have pk₁₆ : PK s₁ s₆ := S.inv.pk.trans (pk₅.trans pk₆)
  refine WP.block_append_iff.mpr (WP.mono (sivOut_wp L E₆ (by rw [pk₁₆.wr, S.en.wr]; exact hV))
    fun s₇ ⟨pk₇, f₇, v₇⟩ => ?_)
  have E₇ := E₆.of_pk pk₇
  have pk₁₇ : PK s₁ s₇ := pk₁₆.trans pk₇
  -- Our caller's registers, in their slots.
  have fm : Frame (mutR c) s₁.mem s₆.mem :=
    ((S.inv.frame.sub mutR_wR).trans (f₅.sub (mutR_oR (by decide)))).trans (f₆.sub mutR_ctrR)
  have sv₇ : Spill.Saved c.W s.gpr savedL s₇.mem :=
    (saved_mut L fm S.en.saved).frame_in savedL_bound f₇ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (L.v_w' (by decide)).symm
  refine WP.mono (exit_wp L E₇ sv₇ (by rw [pk₁₇.sp, S.en.sp])) fun s₈ ⟨ab, m₈, _⟩ => ⟨ab, ?_⟩
  -- The synthetic IV and the ciphertext.
  have v₆ : bytesAt s₆.mem c.W 16 = bytesAt s₅.mem c.W 16 := by
    have := Proof.Cmac.bytesAt_frame f₆ (ctrR_W0 L) (by decide)
    rwa [BitVec.add_zero] at this
  rw [BitVec.add_zero] at v₅ d₆
  rw [Spec.Siv.encryptWith_eq, Spec.Siv.sealWith]
  have hv : bytesAt s₈.mem c.V 16 = Spec.Siv.s2vFinish (Spec.Siv.ctxMac s.mem c.C c.R)
      (Spec.Siv.s2vAcc (Spec.Siv.ctxMac s.mem c.C c.R) (Spec.Siv.components 64 s.mem c.A c.N))
      (bytesAt s.mem c.D c.n) := by
    rw [m₈, v₇, v₆, v₅, wf₄.ctxMac L, wf₄.data L, acc₄]
  have hd : bytesAt s₈.mem c.D c.n = bytesAt s₆.mem c.D c.n := by
    rw [m₈]
    exact Proof.Cmac.bytesAt_frame f₇ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.v_d.symm) (by have := L.n_lt; omega_using [this])
  rw [hv, hd, d₆, wf₅.ctxCiph L, wf₅.data L, v₅, wf₄.ctxMac L, wf₄.data L, acc₄]

end VG.Proof.AesSiv.RISCV64
