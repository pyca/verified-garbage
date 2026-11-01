module

public import VerifiedGarbage.Proof.AesGcmSiv.RISCV64.Env
public import VerifiedGarbage.Proof.AesGcmSiv.RISCV64.Contract
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Fn
public import VerifiedGarbage.Proof.Framework.RISCV64.Bytes
import VerifiedGarbage.Proof.AesGcmSiv.RISCV64.Wp
import VerifiedGarbage.Proof.Framework.RISCV64.Spill
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Cmac.Frame
public import VerifiedGarbage.Impl.AesGcmSiv.RISCV64
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.RISCV64.Target

/-!
# AES-GCM-SIV on RISC-V: the arguments, the entry and the exit

Untrusted: everything here is checked by Lean. The preconditions `sealPre`
and `openPre` give the facts the proofs use about the arguments (`Args`,
`args_of_seal`, `args_of_open`). `entry` loads `work` from the stack, saves
our caller's registers and the return address at `W + 128` as AES-GCM's
functions do (`Proof.AesGcm.RISCV64.save_ok`), keeps the arguments in
`s0`–`s8` and copies the nonce to `W + 1520` (`entry_wp`); AES-GCM's
`restore_ok` is the exit. The pieces write only the parts of `W` in `mutR`,
the data and the stack below `sp`, so the slots stay as the entry left them.
-/

@[expose] public section

namespace VG.Proof.AesGcmSiv.RISCV64

open VG VG.RISCV64 VG.Impl.AesGcmSiv.RISCV64
open VG.Spec.Aes (bytesAt)
open VG.RISCV64.Steps (Upd wp_addSp wp_ld wp_mv)
open VG.Proof.AesGcm.RISCV64 (SavedAt savedR save_ok stkOk stkAll_mem in_off covers_prefix)

/-- The public values of the arguments of `s`. -/
def cxOf (s : State) : Cx where
  K := s.gpr .a0
  W := stackArg s 0
  N := s.gpr .a2
  A := s.gpr .a3
  D := s.gpr .a5
  T := s.gpr .a7
  SP := s.sp
  R := (s.gpr .a1).toNat
  al := (s.gpr .a4).toNat
  n := (s.gpr .a6).toNat

/-- What `seal` and `open` are given: the public values `c`. -/
structure Args (c : Cx) (s : State) : Prop where
  lay : Lay c
  a0 : s.gpr .a0 = c.K
  a1 : s.gpr .a1 = BitVec.ofNat 64 c.R
  a2 : s.gpr .a2 = c.N
  a3 : s.gpr .a3 = c.A
  a4 : s.gpr .a4 = BitVec.ofNat 64 c.al
  a5 : s.gpr .a5 = c.D
  a6 : s.gpr .a6 = BitVec.ofNat 64 c.n
  a7 : s.gpr .a7 = c.T
  w : stackArg s 0 = c.W
  sp : s.sp = c.SP
  perm : Perm c s
  argsC : Covers [args s] (s.rd ++ s.wr)

theorem ofNat_toNat64 (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by simp

theorem covers_of_mem {r : Region} {rs : List Region} (h : r ∈ rs) : Covers [r] rs := fun _ _ ⟨r', hr', hc⟩ => by
  simp only [List.mem_singleton] at hr'; subst hr'; exact ⟨_, h, hc⟩

/-- `Args` from the layout, with the buffers covered as each function's
permissions say. -/
theorem args_of_lay {s : State} (h : oneLay s)
    (hk : Covers [⟨s.gpr .a0, 240⟩] (s.rd ++ s.wr)) (hN : Covers [⟨s.gpr .a2, 12⟩] (s.rd ++ s.wr))
    (hA : Covers [⟨s.gpr .a3, (s.gpr .a4).toNat⟩] (s.rd ++ s.wr)) (ha : Covers [args s] (s.rd ++ s.wr))
    (hT : Covers [⟨s.gpr .a7, 16⟩] (s.rd ++ s.wr))
    (hD : Covers [⟨s.gpr .a5, (s.gpr .a6).toNat⟩] s.wr) (hW : Covers [⟨stackArg s 0, 3840⟩] s.wr) :
    Args (cxOf s) s := by
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, _, _, b1, b2, b3, b4, b5, b6, _, wal, hR, stk⟩ := h
  have bm : ∀ {r : Region}, r ∈ [(⟨s.gpr .a0, 240⟩ : Region), ⟨s.gpr .a2, 12⟩,
      ⟨s.gpr .a3, (s.gpr .a4).toNat⟩, ⟨s.gpr .a5, (s.gpr .a6).toNat⟩, ⟨s.gpr .a7, 16⟩, ⟨stackArg s 0, 3840⟩,
      args s] → (below s.sp 2048).Disjoint r := fun hr => stkAll_mem stk.2.2 hr
  exact {
    lay := ⟨b1, b6, b2, b3, b4, b5, d2, d1, d4, d3, d6, d5, d9, d8, d7, hR, BitVec.isLt _, BitVec.isLt _, wal,
      stk.1, stk.2.1, bm (r := ⟨stackArg s 0, 3840⟩) (by simp), bm (r := ⟨s.gpr .a3, (s.gpr .a4).toNat⟩) (by simp),
      bm (r := ⟨s.gpr .a5, (s.gpr .a6).toNat⟩) (by simp)⟩
    a0 := rfl
    a1 := (ofNat_toNat64 _).symm
    a2 := rfl
    a3 := rfl
    a4 := (ofNat_toNat64 _).symm
    a5 := rfl
    a6 := (ofNat_toNat64 _).symm
    a7 := rfl
    w := rfl
    sp := rfl
    perm := ⟨hk, hW, hN, hA, hD, hT⟩
    argsC := ha }

/-- `seal`'s arguments, and its tag, to write. -/
theorem args_of_seal {s : State} (h : sealPre s) : Args (cxOf s) s ∧ Covers [⟨s.gpr .a7, 16⟩] s.wr := by
  obtain ⟨hrd, hwr, _, hl⟩ := h
  have mrd : ∀ r ∈ [(⟨s.gpr .a0, 240⟩ : Region), ⟨s.gpr .a2, 12⟩, ⟨s.gpr .a3, (s.gpr .a4).toNat⟩, args s],
      Covers [r] (s.rd ++ s.wr) := fun r hr => covers_of_mem (List.mem_append_left _ (by rw [hrd]; exact hr))
  have mwr : ∀ r ∈ [(⟨s.gpr .a5, (s.gpr .a6).toNat⟩ : Region), ⟨s.gpr .a7, 16⟩, ⟨stackArg s 0, 3840⟩],
      Covers [r] s.wr := fun r hr => covers_of_mem (by rw [hwr]; exact hr)
  exact ⟨args_of_lay hl (mrd _ (by simp)) (mrd _ (by simp)) (mrd _ (by simp)) (mrd _ (by simp))
    (Covers.right (mwr _ (by simp))) (mwr _ (by simp)) (mwr _ (by simp)), mwr _ (by simp)⟩

/-- `open`'s arguments, with the received tag to read. -/
theorem args_of_open {s : State} (h : openPre s) : Args (cxOf s) s := by
  obtain ⟨hrd, hwr, hl⟩ := h
  have mrd : ∀ r ∈ [(⟨s.gpr .a0, 240⟩ : Region), ⟨s.gpr .a2, 12⟩, ⟨s.gpr .a3, (s.gpr .a4).toNat⟩,
      ⟨s.gpr .a7, 16⟩, args s], Covers [r] (s.rd ++ s.wr) := fun r hr =>
    covers_of_mem (List.mem_append_left _ (by rw [hrd]; exact hr))
  have mwr : ∀ r ∈ [(⟨s.gpr .a5, (s.gpr .a6).toNat⟩ : Region), ⟨stackArg s 0, 3840⟩], Covers [r] s.wr :=
    fun r hr => covers_of_mem (by rw [hwr]; exact hr)
  exact args_of_lay hl (mrd _ (by simp)) (mrd _ (by simp)) (mrd _ (by simp)) (mrd _ (by simp)) (mrd _ (by simp))
    (mwr _ (by simp)) (mwr _ (by simp))

/-! ## What the pieces write -/

/-- What the pieces write: the parts of `W` below the slots and above them,
the data and the stack below `sp`. -/
abbrev mutR (c : Cx) : List Region :=
  [⟨c.W, 128⟩, ⟨c.W + BitVec.ofNat 64 240, 3600⟩, ⟨c.D, c.n⟩, below c.SP 2048]

theorem sub_lo {c : Cx} {d k : Nat} (h : d + k ≤ 128) :
    ∃ r' ∈ mutR c, Region.Sub ⟨c.W + BitVec.ofNat 64 d, k⟩ r' :=
  ⟨⟨c.W, 128⟩, by simp, Offset.sub_base _ h⟩

theorem sub_hi {c : Cx} {d k : Nat} (h₁ : 240 ≤ d) (h₂ : d + k ≤ 3840) :
    ∃ r' ∈ mutR c, Region.Sub ⟨c.W + BitVec.ofNat 64 d, k⟩ r' :=
  ⟨⟨c.W + BitVec.ofNat 64 240, 3600⟩, by simp, Offset.sub _ h₁ (by omega)⟩

theorem sub_data {c : Cx} : ∃ r' ∈ mutR c, Region.Sub ⟨c.D, c.n⟩ r' := ⟨_, by simp, fun _ h => h⟩

theorem sub_below {c : Cx} : ∃ r' ∈ mutR c, Region.Sub (below c.SP 2048) r' := ⟨_, by simp, fun _ h => h⟩

/-- A buffer missing `W`, the data and the stack below `sp` misses what the
pieces write. -/
theorem buf_mut {c : Cx} {P : Addr} {k : Nat} (hw : (⟨P, k⟩ : Region).Disjoint ⟨c.W, 3840⟩)
    (hd : (⟨P, k⟩ : Region).Disjoint ⟨c.D, c.n⟩) (hb : (below c.SP 2048).Disjoint ⟨P, k⟩) :
    ∀ r ∈ mutR c, (⟨P, k⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hw.sub_right (Region.sub_prefix (by decide))
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hd
  · exact hb.symm

/-- The slots are kept by what the pieces write. -/
theorem slots_mut {c : Cx} (L : Lay c) : ∀ r ∈ mutR c, (savedR c.W).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (Lay.w0_w (c := c) (n := 128) (d := 128) (k := 104) (Nat.le_refl _) (by decide)).symm
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.d_w' (by decide)).symm
  · exact (L.b_w' (by decide)).symm

/-- Our caller's registers, kept in their slots by writes to `mutR`. -/
theorem saved_mut {c : Cx} (L : Lay c) {s₀ : State} {m m' : Mem} (hf : Frame (mutR c) m m')
    (h : SavedAt m c.W s₀) : SavedAt m' c.W s₀ :=
  h.frame hf (slots_mut L)

/-! ## Copies of bytes -/

/-- `copyBytes` of `n` bytes from `S` to a part `D` apart from it. -/
theorem copy_wp {s : State} {src dst : Reg} {soff doff n : Nat} {S D : Addr}
    (hts : Reg.t0 ≠ src) (htd : Reg.t0 ≠ dst) (hso : soff + n ≤ 2048) (hdo : doff + n ≤ 2048) (hn : n ≤ 16)
    (hs : s.gpr src + BitVec.ofNat 64 soff = S) (hd : s.gpr dst + BitVec.ofNat 64 doff = D)
    (hr : Covers [⟨S, n⟩] (s.rd ++ s.wr)) (hw : Covers [⟨D, n⟩] s.wr) (hsep : (⟨S, n⟩ : Region).Disjoint ⟨D, n⟩) :
    WP isa (.block (Impl.Words.RISCV64.copyBytes .t0 src dst soff doff n)) s fun s' =>
      Bytes.Keep .t0 s s' ∧ bytesAt s'.mem D n = bytesAt s.mem S n ∧ Frame [⟨D, n⟩] s.mem s'.mem := by
  refine WP.mono (Bytes.copyBytes_ok hts htd hso hdo (fun i hi => ?_) (fun i hi => ?_) (fun i hi hc => ?_))
    fun s' C => ⟨C.toKeep, ?_, by have := C.frame; rwa [hd] at this⟩
  · rw [← Offset.add_add, hs]; exact in_off hr (d := i) (n := 1) (by omega) (by omega)
  · rw [← Offset.add_add, hd]; exact in_off hw (d := i) (n := 1) (by omega) (by omega)
  · rw [hd, ← Offset.add_add, hs] at hc
    exact hsep _ (Offset.contains_base S (show i + 1 ≤ n by omega) (by omega)) hc
  · simp only [bytesAt]
    refine List.map_congr_left fun i hi => ?_
    have := C.copied i (List.mem_range.mp hi)
    rwa [← Offset.add_add, ← Offset.add_add, hs, hd] at this

/-! ## The entry -/

/-- What the entry leaves. -/
structure Entered (c : Cx) (s s₁ : State) : Prop where
  env : Env c s₁
  saved : SavedAt s₁.mem c.W s
  frame : Frame [savedR c.W, ⟨nP c.W, 12⟩] s.mem s₁.mem
  nonce : bytesAt s₁.mem (nP c.W) 12 = bytesAt s.mem c.N 12
  rd : s₁.rd = s.rd
  wr : s₁.wr = s.wr
  sp : s₁.sp = s.sp

theorem entry_wp {c : Cx} {s : State} (Ar : Args c s) : WP isa (.block entry) s (Entered c s) := by
  have L := Ar.lay
  have hww := L.ww
  unfold entry
  rw [List.append_assoc, List.append_assoc]
  refine WP.block_append (wp_addSp (imm := 0) (by decide) fun s₁ u₁ => ?_)
  refine wp_ld (a := stackArgAddr s 0) (by decide) (by rw [u₁.gpr, stackArgAddr, Nat.mul_zero, BitVec.add_zero, BitVec.add_zero])
    (by rw [stackArgAddr, Ar.sp]; exact Spill.al8 (by have := L.spal; omega) (by decide))
    (by rw [u₁.rd, u₁.wr]; simpa using in_off Ar.argsC (d := 0) (n := 8) (by decide) (by decide))
    fun s₂ u₂ => WP.block_nil ?_
  have W₂ : s₂.gpr .t1 = c.W := by rw [u₂.gpr, u₁.mem, ← Ar.w]; rfl
  have rd₂ : s₂.rd = s.rd := by rw [u₂.rd, u₁.rd]
  have wr₂ : s₂.wr = s.wr := by rw [u₂.wr, u₁.wr]
  have g₂ : ∀ r, r ≠ .t1 → s₂.gpr r = s.gpr r := fun r h => by rw [u₂.other _ h, u₁.other _ h]
  refine WP.block_append (WP.mono (save_ok (b := .t1)
    (by rw [W₂, wr₂]; exact covers_prefix Ar.perm.w (by decide)) (by rw [W₂]; exact L.wal))
    fun s₃ ⟨g₃, s0₃, k₃, sv₃, f₃⟩ => ?_)
  rw [W₂] at s0₃ sv₃ f₃
  rw [u₂.mem, u₁.mem] at f₃
  refine WP.block_append (wp_mv fun s₄ u₄ => wp_mv fun s₅ u₅ => wp_mv fun s₆ u₆ => wp_mv fun s₇ u₇ =>
    wp_mv fun s₈ u₈ => wp_mv fun s₉ u₉ => wp_mv fun s₁₀ u₁₀ => wp_mv fun s₁₁ u₁₁ => WP.block_nil ?_)
  have gA : ∀ r, r ∉ [Reg.s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8] → s₁₁.gpr r = s₃.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hr
    rw [u₁₁.other _ h8, u₁₀.other _ h7, u₉.other _ h6, u₈.other _ h5, u₇.other _ h4, u₆.other _ h3,
      u₅.other _ h2, u₄.other _ h1]
  have v : ∀ r, r ≠ .s0 → r ≠ .t1 → s₃.gpr r = s.gpr r := fun r h0 h1 => by rw [g₃ r h0, g₂ r h1]
  have s0₁₁ : s₁₁.gpr .s0 = c.W := by rw [gA _ (by decide), s0₃]
  have rd₁₁ : s₁₁.rd = s.rd := by
    rw [u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, k₃.rd, rd₂]
  have wr₁₁ : s₁₁.wr = s.wr := by
    rw [u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, k₃.wr, wr₂]
  have sp₁₁ : s₁₁.sp = s.sp := by
    rw [u₁₁.sp, u₁₀.sp, u₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, k₃.sp, u₂.sp, u₁.sp]
  have m₁₁ : s₁₁.mem = s₃.mem := by
    rw [u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem]
  have s1₁₁ : s₁₁.gpr .s1 = c.N := by
    rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
      u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr,
      v _ (by decide) (by decide), Ar.a2]
  have E₁₁ : Env c s₁₁ := by
    refine ⟨s0₁₁, s1₁₁, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by rw [sp₁₁, Ar.sp], Ar.perm.of_eq rd₁₁ wr₁₁⟩
    · rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
        u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide),
        v _ (by decide) (by decide), Ar.a0]
    · rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
        u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide),
        v _ (by decide) (by decide), Ar.a1]
    · rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
        u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        v _ (by decide) (by decide), Ar.a3]
    · rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr,
        u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        v _ (by decide) (by decide), Ar.a4]
    · rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.gpr, u₈.other _ (by decide),
        u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        v _ (by decide) (by decide), Ar.a5]
    · rw [u₁₁.other _ (by decide), u₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide),
        u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        v _ (by decide) (by decide), Ar.a6]
    · rw [u₁₁.gpr, u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
        u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        v _ (by decide) (by decide), Ar.a7]
  -- The nonce's copy.
  have dN : (⟨c.N, 12⟩ : Region).Disjoint ⟨nP c.W, 12⟩ := L.n_w' (by decide)
  refine WP.mono (copy_wp (S := c.N) (D := nP c.W) (soff := 0) (doff := nO) (n := 12) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by rw [s1₁₁, BitVec.add_zero]) (by rw [s0₁₁, nP]; rfl)
    E₁₁.perm.nc (E₁₁.perm.wC (d := 1520) (by decide)) dN) fun s' ⟨K, hb, hf⟩ => ?_
  have pk : PK s₁₁ s' := ⟨K.rd, K.wr, K.sp, fun r hr => K.gpr r (by revert r hr; decide)⟩
  have dS : ∀ r ∈ [(⟨nP c.W, 12⟩ : Region)], (savedR c.W).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide)
  have nN : bytesAt s₁₁.mem c.N 12 = bytesAt s.mem c.N 12 := by
    rw [m₁₁]
    exact Proof.Cmac.bytesAt_frame f₃ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.n_w' (by decide)) (by decide)
  have sv : SavedAt s'.mem c.W s := fun p hp => by
    rw [(sv₃.frame (by rw [← m₁₁]; exact hf) dS) p hp]
    exact g₂ _ ((show ∀ q ∈ Impl.AesGcm.RISCV64.saved, q.1 ≠ .t1 by decide) p hp)
  refine ⟨E₁₁.of_pk pk, sv, ?_, by rw [hb, nN], by rw [pk.rd, rd₁₁],
    by rw [pk.wr, wr₁₁], by rw [pk.sp, sp₁₁]⟩
  rw [← m₁₁] at f₃
  exact (f₃.mono fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp).trans
    (hf.mono fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp)

end VG.Proof.AesGcmSiv.RISCV64
