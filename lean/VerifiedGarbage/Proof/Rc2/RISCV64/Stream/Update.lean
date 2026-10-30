module

import VerifiedGarbage.Proof.Rc2.RISCV64.Stream.Copy
public import VerifiedGarbage.Proof.Rc2.RISCV64.Stream.Checks
public import VerifiedGarbage.Proof.Rc2.RISCV64.Cbc.Verified
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
import VerifiedGarbage.Proof.Rc2.Stream
import VerifiedGarbage.Proof.Rc2.Memory
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Impl.Rc2.RISCV64.Stream
public import VerifiedGarbage.Proof.Framework.RISCV64.Keep
import VerifiedGarbage.Proof.Framework.RISCV64.Spill
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Rc2.RISCV64.Cbc.Lit

/-! # Streaming RC2-CBC on RISCV64: `update` -/

@[expose] public section

namespace VG.Proof.Rc2.RISCV64.Stream

open VG VG.RISCV64 VG.Impl.Rc2.RISCV64 VG.Impl.Rc2.RISCV64.Stream
open VG.Impl.Rc2.RISCV64.Cbc (mov)
open VG.WriteBytes (writeBytes writeBytes_frame)

/-- `update`'s buffers: the context at `ctx` (`a0`), `pending_len` (`a1`),
`len` (`a3`) bytes of data at `a2`, `out_len` (`a5`) bytes of output at `a4`
and the working space at `a6`. -/
structure UpdatePre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .a2, (s.gpr .a3).toNat⟩]
  wr : s.wr = [⟨s.gpr .a0, 144⟩, ⟨s.gpr .a4, (s.gpr .a5).toNat⟩, ⟨s.gpr .a6, 576⟩]
  CD : (⟨s.gpr .a0, 144⟩ : Region).Disjoint ⟨s.gpr .a2, (s.gpr .a3).toNat⟩
  CO : (⟨s.gpr .a0, 144⟩ : Region).Disjoint ⟨s.gpr .a4, (s.gpr .a5).toNat⟩
  CW : (⟨s.gpr .a0, 144⟩ : Region).Disjoint ⟨s.gpr .a6, 576⟩
  DO : (⟨s.gpr .a2, (s.gpr .a3).toNat⟩ : Region).Disjoint ⟨s.gpr .a4, (s.gpr .a5).toNat⟩
  DW : (⟨s.gpr .a2, (s.gpr .a3).toNat⟩ : Region).Disjoint ⟨s.gpr .a6, 576⟩
  OW : (⟨s.gpr .a4, (s.gpr .a5).toNat⟩ : Region).Disjoint ⟨s.gpr .a6, 576⟩
  fitD : (s.gpr .a2).toNat + (s.gpr .a3).toNat ≤ 2 ^ 64
  fitO : (s.gpr .a4).toNat + (s.gpr .a5).toNat ≤ 2 ^ 64
  al : (s.gpr .a6).toNat % 8 = 0
  fitW : (s.gpr .a6).toNat + 576 ≤ 2 ^ 64
  pend : (s.gpr .a1).toNat < 8
  out : (s.gpr .a5).toNat = ((s.gpr .a1).toNat + (s.gpr .a3).toNat) / 8 * 8

/-- `update`'s postcondition. -/
noncomputable def updatePost (d : Spec.Rc2.Direction) (s s' : State) : Prop :=
  let result := Spec.Rc2.update (Spec.Rc2.contextAt s.mem (s.gpr .a0) d (s.gpr .a1).toNat)
    (Spec.Rc2.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat)
  Spec.Rc2.contextAt s'.mem (s.gpr .a0) d (((s.gpr .a1).toNat + (s.gpr .a3).toNat) % 8) = result.1 ∧
    Spec.Rc2.bytesAt s'.mem (s.gpr .a4) (s.gpr .a5).toNat = result.2

theorem toNat_eq (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := (BitVec.ofNat_toNat _ _).trans (BitVec.setWidth_eq _)

theorem short_wp (d : Spec.Rc2.Direction) (s : State) (h : UpdatePre s) (h0 : (s.gpr .a5).toNat = 0) :
    WP isa short s fun s' => Keep [.a7, .a2, .a3, .t0] s s' ∧ updatePost d s s' := by
  obtain ⟨C, hC⟩ : ∃ C, s.gpr .a0 = C := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, s.gpr .a2 = D := ⟨_, rfl⟩
  have hp := h.pend
  have hout := h.out
  obtain ⟨P, hP⟩ : ∃ P, (s.gpr .a1).toNat = P := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L, (s.gpr .a3).toNat = L := ⟨_, rfl⟩
  have e4 : s.gpr .a1 = BitVec.ofNat 64 P := by rw [← hP, toNat_eq]
  have e6 : s.gpr .a3 = BitVec.ofNat 64 L := by rw [← hL, toNat_eq]
  rw [hP] at hp hout; rw [hL] at hout
  have hs : P + L < 8 := by omega_arith
  have hrd := h.rd; have hwr := h.wr; have CD := h.CD
  simp only [hC, hD, hL] at hrd hwr CD
  unfold short
  apply WP.seq
  refine WP.mono (WP.keep [.t0] (c := .block [.add .t0 .a0 .a1]) (Q := fun t => t.gpr .t0 = C + BitVec.ofNat 64 P ∧
      t.mem = s.mem) (by rrun [hC, e4]) (by rfl) rfl)
    fun t₁ ⟨⟨a₁, m₁⟩, k₁⟩ => ?_
  have pIn : Region.Sub ⟨C + BitVec.ofNat 64 (136 + P), L⟩ ⟨C, 144⟩ := Offset.sub_base C (by omega_arith)
  refine WP.mono (copy_run (src := .a2) (dst := .t0) (cnt := .a3) ⟨by decide, by decide, by decide, by decide,
      by decide, by decide⟩ (dd := 136) (by decide) (A := D) (B := C + BitVec.ofNat 64 (136 + P)) (k := L)
    (by rw [k₁.gpr (by decide), hD]) (by rw [a₁, Offset.add_add, Nat.add_comm])
    (by rw [k₁.gpr (by decide), e6]) (by rw [← hL]; exact (s.gpr .a3).isLt)
    (fun i hi => by rw [k₁.2.1, k₁.2.2, hrd]; exact ⟨⟨D, L⟩, by simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩)
    (fun i hi => by rw [k₁.2.2, hwr]; exact ⟨⟨C, 144⟩, by simp, by rw [Offset.add_add]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩)
    (CD.symm.sub_right pIn)) fun t ⟨_, _, k, m⟩ => ⟨(k₁.trans k).mono (by simp), ?_⟩
  rw [m₁] at m
  have F : Frame [⟨C + BitVec.ofNat 64 (136 + P), L⟩] s.mem t.mem := by
    rw [m]; exact writeBytes_frame _ _ _ (by rw [Proof.Rc2.bytesAt_length]; exact Region.contains_self _ _)
  have e128 : (C + 128 : Addr) = C + BitVec.ofNat 64 128 := rfl
  have e136 : (C + 136 : Addr) = C + BitVec.ofNat 64 136 := rfl
  unfold updatePost
  rw [hC, hD, hP, hL, hout]
  refine Proof.Rc2.update_post_short hs (Proof.Rc2.scheduleAt_frame F C (by
      simp only [List.mem_singleton, forall_eq]; exact Offset.base_disjoint C (by omega_arith) (by omega_arith)))
    (Proof.Rc2.blockAt_frame F _ (by
      simp only [List.mem_singleton, forall_eq]; rw [e128]; exact Offset.disjoint C (by omega_arith) (by omega_arith) (by omega_arith))) ?_
  rw [Proof.Rc2.bytesAt_add, Proof.Rc2.bytesAt_frame F _ P (by omega_arith) (by
      simp only [List.mem_singleton, forall_eq]; rw [e136]; exact Offset.disjoint C (by omega_arith) (by omega_arith) (by omega_arith)),
    e136, Offset.add_add, m]
  congr 1
  have := Proof.Rc2.bytesAt_writeBytes_self s.mem (C + BitVec.ofNat 64 (136 + P)) (Spec.Rc2.bytesAt s.mem D L)
    (by rw [Proof.Rc2.bytesAt_length]; omega_arith)
  rwa [Proof.Rc2.bytesAt_length] at this

theorem cbcCall_eq (d : Spec.Rc2.Direction) : ∃ nm, cbcCall d = .call nm (Cbc.cbc d) := by
  cases d <;> exact ⟨_, rfl⟩

theorem cbc_noFrames (d : Spec.Rc2.Direction) : (Cbc.cbc d).noFrames = true := by
  cases d
  · exact (by lit_decide : Cbc.encrypt.noFrames = true)
  · exact (by lit_decide : Cbc.decrypt.noFrames = true)

theorem long_wp (d : Spec.Rc2.Direction) (s : State) (h : UpdatePre s) (h0 : (s.gpr .a5).toNat ≠ 0) :
    WP isa (long d) s fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.gpr .ra = s.gpr .ra ∧
      updatePost d s s' := by
  obtain ⟨C, hC⟩ : ∃ C, s.gpr .a0 = C := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, s.gpr .a2 = D := ⟨_, rfl⟩
  obtain ⟨O, hO⟩ : ∃ O, s.gpr .a4 = O := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W, s.gpr .a6 = W := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P, (s.gpr .a1).toNat = P := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L, (s.gpr .a3).toNat = L := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N, (s.gpr .a5).toNat = N := ⟨_, rfl⟩
  have e4 : s.gpr .a1 = BitVec.ofNat 64 P := by rw [← hP, toNat_eq]
  have e6 : s.gpr .a3 = BitVec.ofNat 64 L := by rw [← hL, toNat_eq]
  have e8 : s.gpr .a5 = BitVec.ofNat 64 N := by rw [← hN, toNat_eq]
  have hp := h.pend; have hout := h.out; have fitD := h.fitD; have fitO := h.fitO
  have hrd := h.rd; have hwr := h.wr; have CD := h.CD; have CO := h.CO; have CW := h.CW; have DO := h.DO
  have DW := h.DW; have OW := h.OW; have hal := h.al; have fitW := h.fitW
  simp only [hC, hD, hO, hW, hP, hL, hN] at hp hout fitD fitO hrd hwr CD CO CW DO DW OW hal fitW
  rw [hN] at h0
  have hL' : L < 2 ^ 64 := by rw [← hL]; exact (s.gpr .a3).isLt
  have hN8 : 8 ≤ N := by omega_arith
  have hPN : P ≤ N := by omega_arith
  have hNL : N - P ≤ L := by omega_arith
  unfold updatePost
  rw [hC, hD, hO, hP, hL, hN]
  have cW : ∀ d, d + 8 ≤ 576 → (⟨W, 576⟩ : Region).Contains (W + BitVec.ofNat 64 d) 8 := fun d hd =>
    Offset.contains_base W hd (by omega_arith)
  have inW : ∀ d, d + 8 ≤ 576 → InRegions s.wr (W + BitVec.ofNat 64 d) 8 := fun d hd => by
    rw [hwr]; exact ⟨⟨W, 576⟩, by simp, cW d hd⟩
  have W512 := inW 512 (by decide)
  have W520 := inW 520 (by decide)
  have al512 := Spill.al8 hal (d := 512) (by decide)
  have al520 := Spill.al8 hal (d := 520) (by decide)
  unfold long withRa
  apply WP.seq
  refine WP.mono (WP.keep [.s7] (c := .block [.store .d .ra .a6 512, .store .d .s7 .a6 520, mov .s7 .a6])
      (Q := fun t => t.gpr .s7 = W ∧
      t.mem = (s.mem.writeW (W + BitVec.ofNat 64 512) (s.gpr .ra)).writeW (W + BitVec.ofNat 64 520) (s.gpr .s7))
    (by rrun [mov, hW, W512, W520, al512, al520]) (by rfl) rfl)
    fun t₀ ⟨⟨a₀, m₀⟩, k₀⟩ => ?_
  have FA : Frame [⟨W, 576⟩] s.mem t₀.mem := by
    rw [m₀]
    exact ((Frame.refl _ _).writeW (r := ⟨W, 576⟩) (by simp) _ (cW 512 (by decide))).writeW
      (r := ⟨W, 576⟩) (by simp) _ (cW 520 (by decide))
  have g₀ : ∀ r, r ∉ [Reg.s7] → t₀.gpr r = s.gpr r := fun r hr => k₀.gpr hr
  apply WP.seq
  apply WP.seq
  -- the pending bytes to `out`
  refine WP.mono (WP.keep [.t0, .t1, .t2] (c := .block toOut) (Q := fun t =>
      t.gpr .t0 = C + BitVec.ofNat 64 136 ∧ t.gpr .t1 = O ∧ t.gpr .t2 = BitVec.ofNat 64 P ∧ t.mem = t₀.mem)
    (by unfold toOut; rrun [mov, g₀ .a0 (by decide), g₀ .a4 (by decide), g₀ .a1 (by decide), hC, hO, e4])
    (by rfl) rfl) fun t₁ ⟨⟨a10, a11, a12, m₁⟩, k₁⟩ => ?_
  have rw₁ : t₁.rd = s.rd ∧ t₁.wr = s.wr := ⟨by rw [k₁.2.1, k₀.2.1], by rw [k₁.2.2, k₀.2.2]⟩
  have inC : ∀ i, 136 + i < 144 → InRegions t₁.wr (C + BitVec.ofNat 64 136 + BitVec.ofNat 64 i) 1 := fun i hi => by
    rw [rw₁.2, hwr, Offset.add_add]; exact ⟨⟨C, 144⟩, by simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  have inO : ∀ i, i < N → InRegions t₁.wr (O + BitVec.ofNat 64 i) 1 := fun i hi => by
    rw [rw₁.2, hwr]; exact ⟨⟨O, N⟩, by simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  have inD : ∀ i, i < L → InRegions (t₁.rd ++ t₁.wr) (D + BitVec.ofNat 64 i) 1 := fun i hi => by
    rw [rw₁.1, hrd]; exact ⟨⟨D, L⟩, by simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  have rd' : ∀ {a}, InRegions t₁.wr a 1 → InRegions (t₁.rd ++ t₁.wr) a 1 := fun ⟨r, hr, hc⟩ =>
    ⟨r, List.mem_append_right _ hr, hc⟩
  apply WP.seq
  refine WP.mono (copy_run (src := .t0) (dst := .t1) (cnt := .t2) ⟨by decide, by decide, by decide, by decide,
      by decide, by decide⟩ (dd := 0) (by decide) (A := C + BitVec.ofNat 64 136) (B := O) (k := P) a10
    (by rw [a11]; simp) a12 (by omega_arith) (fun i hi => rd' (inC i (by omega_arith)))
    (fun i hi => inO i (by omega_arith))
    ((CO.sub_left (Offset.sub_base C (by omega_arith))).sub_right (Region.sub_prefix hPN))) fun t₂ c₂ => ?_
  have rw₂ : t₂.rd = s.rd ∧ t₂.wr = s.wr := ⟨by rw [c₂.keep.2.1, rw₁.1], by rw [c₂.keep.2.2, rw₁.2]⟩
  have kk₂ := (k₀.trans k₁).trans c₂.keep
  apply WP.seq
  refine WP.mono (WP.keep [.t2] (c := .block middle) (Q := fun t =>
      t.gpr .t2 = BitVec.ofNat 64 (N - P) ∧ t.mem = t₂.mem)
    (by unfold middle; rrun [kk₂.gpr (show Reg.a5 ∉ _ by decide), kk₂.gpr (show Reg.a1 ∉ _ by decide), e8, e4,
      Offset.ofNat_sub_ofNat hPN])
    (by rfl) rfl) fun t₃ ⟨⟨a12', m₃⟩, k₃⟩ => ?_
  have kk₃ := kk₂.trans k₃
  have rw₃ : t₃.rd = t₁.rd ∧ t₃.wr = t₁.wr := ⟨by rw [k₃.2.1, c₂.keep.2.1], by rw [k₃.2.2, c₂.keep.2.2]⟩
  -- the first `out_len - pending_len` bytes of data, after them
  apply WP.seq
  refine WP.mono (copy_run (src := .a2) (dst := .t1) (cnt := .t2) ⟨by decide, by decide, by decide, by decide,
      by decide, by decide⟩ (dd := 0) (by decide) (A := D) (B := O + BitVec.ofNat 64 P) (k := N - P)
    (by rw [kk₃.gpr (by decide), hD]) (by rw [k₃.gpr (by decide), c₂.pdst, a11]; simp) a12' (by omega_arith)
    (fun i hi => by rw [rw₃.1, rw₃.2]; exact inD i (by omega_arith))
    (fun i hi => by rw [rw₃.2, Offset.add_add]; exact inO _ (by omega_arith))
    ((DO.sub_left (Region.sub_prefix hNL)).sub_right (Offset.sub_base O (by omega_arith)))) fun t₄ c₄ => ?_
  have kk₄ := kk₃.trans c₄.keep
  have rw₄ : t₄.rd = t₁.rd ∧ t₄.wr = t₁.wr := ⟨by rw [c₄.keep.2.1, rw₃.1], by rw [c₄.keep.2.2, rw₃.2]⟩
  -- the rest of the data to the pending bytes
  have eR : BitVec.ofNat 64 L - BitVec.ofNat 64 N + BitVec.ofNat 64 P = BitVec.ofNat 64 ((P + L) % 8) := by
    rw [← Offset.add_sub_comm, BitVec.ofNat_add_ofNat, Offset.ofNat_sub_ofNat (by omega_arith)]
    exact congrArg (BitVec.ofNat 64) (by omega_arith)
  apply WP.seq
  refine WP.mono (WP.keep [.t0, .t2] (c := .block toPending) (Q := fun t =>
      t.gpr .t0 = C + BitVec.ofNat 64 136 ∧ t.gpr .t2 = BitVec.ofNat 64 ((P + L) % 8) ∧ t.mem = t₄.mem)
    (by unfold toPending; rrun [kk₄.gpr (show Reg.a0 ∉ _ by decide), kk₄.gpr (show Reg.a3 ∉ _ by decide),
      kk₄.gpr (show Reg.a5 ∉ _ by decide), kk₄.gpr (show Reg.a1 ∉ _ by decide), hC, e6, e8, e4, eR])
    (by rfl) rfl) fun t₅ ⟨⟨a10', a12'', m₅⟩, k₅⟩ => ?_
  have kk₅ := kk₄.trans k₅
  have rw₅ : t₅.rd = t₁.rd ∧ t₅.wr = t₁.wr := ⟨by rw [k₅.2.1, rw₄.1], by rw [k₅.2.2, rw₄.2]⟩
  apply WP.seq
  refine WP.mono (copy_run (src := .a2) (dst := .t0) (cnt := .t2) ⟨by decide, by decide, by decide, by decide,
      by decide, by decide⟩ (dd := 0) (by decide) (A := D + BitVec.ofNat 64 (N - P)) (B := C + BitVec.ofNat 64 136)
    (k := (P + L) % 8) (by rw [k₅.gpr (by decide), c₄.psrc]) (by rw [a10']; simp) a12'' (by omega_arith)
    (fun i hi => by rw [rw₅.1, rw₅.2, Offset.add_add]; exact inD _ (by omega_arith))
    (fun i hi => by rw [rw₅.2]; exact inC i (by omega_arith))
    ((CD.symm.sub_left (Offset.sub_base D (by omega_arith))).sub_right (Offset.sub_base C (by omega_arith)))) fun t₆ c₆ => ?_
  have kk₆ := kk₅.trans c₆.keep
  have rw₆ : t₆.rd = t₁.rd ∧ t₆.wr = t₁.wr := ⟨by rw [c₆.keep.2.1, rw₅.1], by rw [c₆.keep.2.2, rw₅.2]⟩
  have shr3 : BitVec.ofNat 64 N >>> 3 = BitVec.ofNat 64 (N / 8) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    rw [Nat.mod_eq_of_lt (show N < 2 ^ 64 by omega_arith), Nat.mod_eq_of_lt (show N / 2 ^ 3 < 2 ^ 64 by omega_arith)]
  apply WP.seq
  refine WP.mono (WP.keep [.a1, .a2, .a3, .a4] (c := .block cbcArgs) (Q := fun t =>
      t.gpr .a0 = C ∧ t.gpr .a1 = C + 128#64 ∧ t.gpr .a2 = O ∧ t.gpr .a3 = BitVec.ofNat 64 (N / 8) ∧
        t.gpr .a4 = W ∧ t.mem = t₆.mem)
    (by unfold cbcArgs; rrun [mov, kk₆.gpr (show Reg.a0 ∉ _ by decide), kk₆.gpr (show Reg.a4 ∉ _ by decide),
      kk₆.gpr (show Reg.a5 ∉ _ by decide), kk₆.gpr (show Reg.a6 ∉ _ by decide), hC, hO, e8, hW, shr3])
    (by rfl) rfl)
    fun t₇ ⟨⟨b3, b4, b5, b6, b7, m₇⟩, k₇⟩ => ?_
  have rw₇ : t₇.rd = s.rd ∧ t₇.wr = s.wr := ⟨by rw [k₇.2.1, rw₆.1, rw₁.1], by rw [k₇.2.2, rw₆.2, rw₁.2]⟩
  have hn8 : 8 * (N / 8) = N := by omega_arith
  have hn6 : (BitVec.ofNat 64 (N / 8)).toNat = N / 8 := by rw [BitVec.toNat_ofNat]; omega_arith
  have C128 : Region.Sub ⟨C, 128⟩ ⟨C, 144⟩ := Region.sub_prefix (by decide)
  have Cv : Region.Sub ⟨C + 128#64, 8⟩ ⟨C, 144⟩ := Offset.sub_base C (d := 128) (by omega_arith)
  have W512r : Region.Sub ⟨W, 512⟩ ⟨W, 576⟩ := Region.sub_prefix (by decide)
  obtain ⟨nm, ecall⟩ := cbcCall_eq d
  rw [ecall]
  refine WP.call (k := Cbc.cbcC d) (Cbc.cbc_ok d) (rd := [⟨C, 128⟩]) (wr := [⟨C + 128#64, 8⟩, ⟨O, 8 * (N / 8)⟩,
      ⟨W, 512⟩]) ?_ ?_ ?_ (fun t₈ rd₈ wr₈ _ F₈ P₈ _ post₈ => ?_) (cbc_noFrames d)
  · simp only [Cbc.cbcC, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr]
    rw [State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide),
      State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide), b3, b4, b5, b6, b7, hn6, hn8]
    exact ⟨rfl, rfl, hal, Offset.base_disjoint C (e := 128) (by omega_arith) (by omega_arith), CO.sub_left C128,
      CW.sub_left C128 |>.sub_right W512r, CO.sub_left Cv, (CW.sub_left Cv).sub_right W512r, OW.sub_right W512r,
      by omega_arith, by omega_arith⟩
  · rw [rw₇.1, rw₇.2, hrd, hwr, hn8]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨⟨C, 144⟩, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
    · exact ⟨⟨C, 144⟩, by simp, 128, rfl, by simp⟩
    · exact ⟨⟨O, N⟩, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
    · exact ⟨⟨W, 576⟩, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
  · rw [rw₇.2, hwr, hn8]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨⟨C, 144⟩, by simp, 128, rfl, by simp⟩
    · exact ⟨⟨O, N⟩, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
    · exact ⟨⟨W, 576⟩, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
  -- the frames of the copies
  have F₂ : Frame [⟨O, P⟩] t₁.mem t₂.mem := by
    rw [c₂.mem]; exact writeBytes_frame _ _ _ (by rw [Proof.Rc2.bytesAt_length]; exact Region.contains_self _ _)
  have F₄ : Frame [⟨O + BitVec.ofNat 64 P, N - P⟩] t₃.mem t₄.mem := by
    rw [c₄.mem]; exact writeBytes_frame _ _ _ (by rw [Proof.Rc2.bytesAt_length]; exact Region.contains_self _ _)
  have F₆ : Frame [⟨C + BitVec.ofNat 64 136, (P + L) % 8⟩] t₅.mem t₆.mem := by
    rw [c₆.mem]; exact writeBytes_frame _ _ _ (by rw [Proof.Rc2.bytesAt_length]; exact Region.contains_self _ _)
  have Cp : Region.Sub ⟨C + BitVec.ofNat 64 136, (P + L) % 8⟩ ⟨C, 144⟩ := Offset.sub_base C (by omega_arith)
  have Op : Region.Sub ⟨O, P⟩ ⟨O, N⟩ := Region.sub_prefix hPN
  have Om : Region.Sub ⟨O + BitVec.ofNat 64 P, N - P⟩ ⟨O, N⟩ := Offset.sub_base O (by omega_arith)
  have FS : Frame [⟨W, 576⟩, ⟨O, N⟩, ⟨C + BitVec.ofNat 64 136, (P + L) % 8⟩] s.mem t₇.mem := by
    have f₁ : Frame [⟨W, 576⟩, ⟨O, N⟩, ⟨C + BitVec.ofNat 64 136, (P + L) % 8⟩] s.mem t₁.mem := by
      rw [m₁]; exact FA.mono (by simp)
    have f₂ : Frame [⟨W, 576⟩, ⟨O, N⟩, ⟨C + BitVec.ofNat 64 136, (P + L) % 8⟩] s.mem t₂.mem :=
      f₁.trans (F₂.sub fun r hr => ⟨⟨O, N⟩, by simp, by simp at hr; subst hr; exact Op⟩)
    have f₄ : Frame [⟨W, 576⟩, ⟨O, N⟩, ⟨C + BitVec.ofNat 64 136, (P + L) % 8⟩] s.mem t₄.mem :=
      (m₃ ▸ f₂).trans (F₄.sub fun r hr => ⟨⟨O, N⟩, by simp, by simp at hr; subst hr; exact Om⟩)
    rw [m₇]
    exact (m₅ ▸ f₄).trans (F₆.mono (by simp))
  have FT : Frame [⟨O, N⟩, ⟨C + BitVec.ofNat 64 136, (P + L) % 8⟩] t₀.mem t₇.mem := by
    have f₂ : Frame [⟨O, N⟩, ⟨C + BitVec.ofNat 64 136, (P + L) % 8⟩] t₀.mem t₂.mem := by
      rw [← m₁]; exact F₂.sub fun r hr => ⟨⟨O, N⟩, by simp, by simp at hr; subst hr; exact Op⟩
    have f₄ : Frame [⟨O, N⟩, ⟨C + BitVec.ofNat 64 136, (P + L) % 8⟩] t₀.mem t₄.mem :=
      (m₃ ▸ f₂).trans (F₄.sub fun r hr => ⟨⟨O, N⟩, by simp, by simp at hr; subst hr; exact Om⟩)
    rw [m₇]
    exact (m₅ ▸ f₄).trans (F₆.mono (by simp))
  have h31 : t₈.gpr .s7 = W := by
    rw [P₈ _ (by decide), k₇.gpr (by decide), c₆.keep.gpr (by decide), k₅.gpr (by decide), c₄.keep.gpr (by decide),
      k₃.gpr (by decide), c₂.keep.gpr (by decide), k₁.gpr (by decide), a₀]
  have slot : ∀ d, 512 ≤ d → d + 8 ≤ 576 →
      t₈.mem.readW (W + BitVec.ofNat 64 d) 64 = t₀.mem.readW (W + BitVec.ofNat 64 d) 64 := by
    intro d hd hd'
    have sd : Region.Sub ⟨W + BitVec.ofNat 64 d, 8⟩ ⟨W, 576⟩ := Offset.sub_base W (by omega_arith)
    rw [F₈.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl)
      · exact (CW.sub_left Cv).symm.sub_left sd
      · rw [hn8]; exact OW.symm.sub_left sd
      · exact Offset.disjoint_base W (by omega_arith) (by omega_arith)) (by decide),
      FT.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · exact OW.symm.sub_left sd
      · exact (CW.sub_left Cp).symm.sub_left sd) (by decide)]
  have e512 : t₈.mem.readW (W + 512#64) 64 = s.gpr .ra := by
    rw [slot 512 (by decide) (by decide), m₀, Mem.readW_writeW_sep (Offset.sep W (by omega_arith) (by omega_arith) (by omega_arith))
      (by decide), Mem.readW_writeW_self64]
  have e520 : t₈.mem.readW (W + 520#64) 64 = s.gpr .s7 := by
    rw [slot 520 (by decide) (by decide), m₀, Mem.readW_writeW_self64]
  have in512 : InRegions (t₈.rd ++ t₈.wr) (W + 512#64) 8 := by
    rw [rd₈, wr₈, rw₇.1, rw₇.2]; obtain ⟨r, hr, hc⟩ := W512; exact ⟨r, List.mem_append_right _ hr, hc⟩
  have in520 : InRegions (t₈.rd ++ t₈.wr) (W + 520#64) 8 := by
    rw [rd₈, wr₈, rw₇.1, rw₇.2]; obtain ⟨r, hr, hc⟩ := W520; exact ⟨r, List.mem_append_right _ hr, hc⟩
  refine WP.mono (WP.keep [.ra, .s7] (c := .block [.load .d .ra .s7 512, .load .d .s7 .s7 520])
      (Q := fun t => t.gpr .s7 = s.gpr .s7 ∧ t.gpr .ra = s.gpr .ra ∧ t.mem = t₈.mem)
    (by rrun [h31, e512, e520, in512, in520, al512, al520]) (by rfl) rfl)
    fun t₉ ⟨⟨a31, lr₉, m₉⟩, k₉⟩ => ⟨fun r hr => ?_, lr₉, ?_⟩
  · by_cases h31' : r = .s7
    · subst h31'; exact a31
    · have kk₇ := kk₆.trans k₇
      have hn : r ∉ [Reg.ra, .s7, .a7, .t0, .t1, .t2, .a2, .a3, .a1, .a4] := by revert hr h31'; revert r; decide
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
      rw [k₉.gpr (by simp [hn]), P₈ r hr, kk₇.gpr (by simp [hn])]
  · have e136 : (C + 136 : Addr) = C + BitVec.ofNat 64 136 := rfl
    have e128 : (C + 128 : Addr) = C + 128#64 := rfl
    have sglt : ∀ {X Y : Region}, X.Disjoint Y → ∀ r ∈ [Y], X.Disjoint r := fun h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h
    -- the bytes copied to `out`
    have hA : Spec.Rc2.bytesAt t₇.mem O N =
        Spec.Rc2.bytesAt s.mem (C + 136) P ++ Spec.Rc2.bytesAt s.mem D (N - P) := by
      have q₁ : Spec.Rc2.bytesAt t₇.mem O N = Spec.Rc2.bytesAt t₄.mem O N := by
        rw [m₇, Proof.Rc2.bytesAt_frame F₆ O N (by omega_arith) (sglt (CO.sub_left Cp).symm), m₅]
      have q₂ : Spec.Rc2.bytesAt t₄.mem O P = Spec.Rc2.bytesAt s.mem (C + 136) P := by
        rw [Proof.Rc2.bytesAt_frame F₄ O P (by omega_arith) (sglt (Offset.base_disjoint O (by omega_arith) (by omega_arith))), m₃, c₂.mem]
        have := Proof.Rc2.bytesAt_writeBytes_self t₁.mem O (Spec.Rc2.bytesAt t₁.mem (C + BitVec.ofNat 64 136) P)
          (by rw [Proof.Rc2.bytesAt_length]; omega_arith)
        rw [Proof.Rc2.bytesAt_length] at this
        rw [this, m₁, e136, Proof.Rc2.bytesAt_frame FA _ P (by omega_arith)
          (sglt ((CW.sub_left (Offset.sub_base C (by omega_arith))) : Region.Disjoint ⟨C + BitVec.ofNat 64 136, P⟩ _))]
      have q₃ : Spec.Rc2.bytesAt t₄.mem (O + BitVec.ofNat 64 P) (N - P) = Spec.Rc2.bytesAt s.mem D (N - P) := by
        rw [c₄.mem]
        have := Proof.Rc2.bytesAt_writeBytes_self t₃.mem (O + BitVec.ofNat 64 P) (Spec.Rc2.bytesAt t₃.mem D (N - P))
          (by rw [Proof.Rc2.bytesAt_length]; omega_arith)
        rw [Proof.Rc2.bytesAt_length] at this
        rw [this, m₃, Proof.Rc2.bytesAt_frame F₂ D _ (by omega_arith) (sglt ((DO.sub_left (Region.sub_prefix hNL)).sub_right Op)),
          m₁, Proof.Rc2.bytesAt_frame FA D _ (by omega_arith) (sglt (DW.sub_left (Region.sub_prefix hNL)))]
      rw [q₁, show N = P + (N - P) by omega_arith, Proof.Rc2.bytesAt_add, Nat.add_sub_cancel_left, q₂, q₃]
    have hs₁ : Spec.Rc2.scheduleAt t₇.mem C = Spec.Rc2.scheduleAt s.mem C :=
      Proof.Rc2.scheduleAt_frame FS C (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro r (rfl | rfl | rfl)
        · exact CW.sub_left C128
        · exact CO.sub_left C128
        · exact Offset.base_disjoint C (by omega_arith) (by omega_arith))
    have hiv₁ : Spec.Rc2.blockAt t₇.mem (C + 128) = Spec.Rc2.blockAt s.mem (C + 128) :=
      Proof.Rc2.blockAt_frame FS _ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro r (rfl | rfl | rfl)
        · exact CW.sub_left Cv
        · exact CO.sub_left Cv
        · rw [e128]; exact Offset.disjoint C (by omega_arith) (by omega_arith) (by omega_arith))
    have hF₈ : ∀ X : Region, Region.Sub X ⟨C, 144⟩ → X.Disjoint ⟨C + 128#64, 8⟩ →
        ∀ r ∈ [(⟨C + 128#64, 8⟩ : Region), ⟨O, 8 * (N / 8)⟩, ⟨W, 512⟩], X.Disjoint r := fun X hX h₁ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h₁
      · rw [hn8]; exact CO.sub_left hX
      · exact (CW.sub_left hX).sub_right W512r
    have hpend : Spec.Rc2.bytesAt t₉.mem (C + 136) ((P + L) % 8) =
        Spec.Rc2.bytesAt s.mem (D + BitVec.ofNat 64 (N - P)) ((P + L) % 8) := by
      rw [m₉, e136, Proof.Rc2.bytesAt_frame F₈ _ _ (by omega_arith)
        (hF₈ _ Cp (Offset.disjoint C (by omega_arith) (by omega_arith) (by omega_arith))), m₇, c₆.mem]
      have := Proof.Rc2.bytesAt_writeBytes_self t₅.mem (C + BitVec.ofNat 64 136)
        (Spec.Rc2.bytesAt t₅.mem (D + BitVec.ofNat 64 (N - P)) ((P + L) % 8)) (by rw [Proof.Rc2.bytesAt_length]; omega_arith)
      rw [Proof.Rc2.bytesAt_length] at this
      have Dr : Region.Sub ⟨D + BitVec.ofNat 64 (N - P), (P + L) % 8⟩ ⟨D, L⟩ := Offset.sub_base D (by omega_arith)
      rw [this, m₅, Proof.Rc2.bytesAt_frame F₄ _ _ (by omega_arith) (sglt ((DO.sub_left Dr).sub_right Om)), m₃,
        Proof.Rc2.bytesAt_frame F₂ _ _ (by omega_arith) (sglt ((DO.sub_left Dr).sub_right Op)), m₁,
        Proof.Rc2.bytesAt_frame FA _ _ (by omega_arith) (sglt (DW.sub_left Dr))]
    have hs : Spec.Rc2.scheduleAt t₉.mem C = Spec.Rc2.scheduleAt t₇.mem C := by
      rw [m₉]
      exact Proof.Rc2.scheduleAt_frame F₈ C (hF₈ _ C128 (Offset.base_disjoint C (e := 128) (by omega_arith) (by omega_arith)))
    have post := post₈
    simp only [Cbc.cbcC, State.withRegions_mem, State.withRegions_gpr, State.callEntry_mem] at post
    rw [State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide),
      State.callEntry_gpr _ (by decide), b3, b4, b5, b6, hn6] at post
    rw [← m₉] at post
    subst hout
    rw [Nat.mul_div_cancel _ (by decide)] at post
    exact Proof.Rc2.update_post_long hp (by omega_arith) hA hs₁ hiv₁ hpend hs post.1 post.2

theorem update_wp (d : Spec.Rc2.Direction) (s : State) (h : UpdatePre s) :
    WP isa (update d) s fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.gpr .ra = s.gpr .ra ∧
      updatePost d s s' := by
  unfold update
  have e8 := toNat_eq (s.gpr .a5)
  refine WP.ite (decide ((s.gpr .a5).toNat = 0))
    (by rw [Steps.eval_zero, ← e8, Steps.ofNat_beq_zero (s.gpr .a5).isLt, e8])
    (fun hb => ?_) (fun hb => long_wp d s h (of_decide_eq_false hb))
  exact WP.mono (short_wp d s h (of_decide_eq_true hb)) fun t ⟨k, p⟩ =>
    ⟨fun r hr => k.gpr (by revert hr; revert r; decide), k.gpr (by decide), p⟩

end VG.Proof.Rc2.RISCV64.Stream
