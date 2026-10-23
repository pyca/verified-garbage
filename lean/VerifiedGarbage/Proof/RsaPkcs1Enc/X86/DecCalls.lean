module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecD
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.HashVp
import VerifiedGarbage.Proof.RsaPkcs1Sig.BytesAt
import VerifiedGarbage.Proof.Hmac.Generic.Common
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecMem

/-!
# RSAES-PKCS1-v1_5 decryption on x86: the calls of SHA-256 and HMAC

The parts of `scratch` the calls use, by their pointers (`sr P o n`): apart
from each other, the stack below the frame and the buffers we only read.
A call changes memory only there, which keeps the private-key operation's
result (`Base.call`). And the arguments of each call (`initA`, `updA`,
`finA`, `hiA`, `hfA`), with the states at `scratch + sSt` (and the outer
state at `scratch + sOuter`) and the working space at `scratch + sW`.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86.Dec

open VG VG.Impl.RsaPkcs1Enc.X86.Decrypt VG.Proof.RsaPkcs1Sig.X86
open VG.X86 hiding frameBytes
open VG.Proof.Sha256.X86.Variants (Backend)
open VG.Proof.Pbkdf2.Stream.X86 (InitArgs UpdArgs FinArgs)
open VG.Proof.Pbkdf2.Whole.X86 (HiArgs HfArgs)

variable {P : EP}

/-- The `n` bytes at `scratch + o`, by the pointer the code computes. -/
abbrev sr (P : EP) (o n : Nat) : Region := ⟨(P.scr + BitVec.ofNat 32 o).setWidth 64, n⟩

namespace In

variable {σ : State} (h : In P σ)
include h

theorem sr_eq {o n : Nat} (ho : o < 8448) : sr P o n = sc P o n := by
  simp only [sr, sc]; rw [h.scrA ho]

theorem sr_fit {o n : Nat} (ho : o < 8448) (hn : o + n ≤ 8448) :
    (P.scr + BitVec.ofNat 32 o).toNat + n ≤ 2 ^ 32 := by
  rw [h.scr_toNat ho]; have := h.scr_fit; have := h.sl8; omega

theorem sr_sep {o n o' n' : Nat} (hs : o + n ≤ o' ∨ o' + n' ≤ o) (ho : o < 8448) (ho' : o' < 8448)
    (h₁ : o + n ≤ 8448) (h₂ : o' + n' ≤ 8448) : (sr P o n).Disjoint (sr P o' n') := by
  rw [h.sr_eq ho, h.sr_eq ho']; exact sc_sep hs h₁ h₂

theorem sr_sub {o n : Nat} (ho : o < 8448) (hn : o + n ≤ 8448) : Region.Sub (sr P o n) P.SCR := by
  rw [h.sr_eq ho]; exact h.sc_sub hn

theorem low_of {k : Nat} (hk : k ≤ 3448) : Region.Sub (below P.B k) P.lay.LOW := by
  rw [← h.ok.low_eq]; exact below_sub hk h.ok.BC

theorem below_sr {k o n : Nat} (hk : k ≤ 3448) (ho : o < 8448) (hn : o + n ≤ 8448) :
    (below P.B k).Disjoint (sr P o n) := by
  rw [h.sr_eq ho]; exact (h.low_sc hn).sub_left (h.low_of hk)

theorem below_ro {k : Nat} (hk : k ≤ 3448) {R : Region} (hR : R ∈ P.ro) : (below P.B k).Disjoint R :=
  (h.ok.low_buf (.inl hR)).sub_left (h.low_of hk)

theorem sr_ro {o n : Nat} (ho : o < 8448) (hn : o + n ≤ 8448) {R : Region} (hR : R ∈ P.ro) :
    (sr P o n).Disjoint R := by
  rw [h.sr_eq ho]; exact h.sc_ro hn hR

theorem sr_safe {o n : Nat} (ho : o < 8448) (hn : o + n ≤ 8448) : Safe P (sr P o n) := by
  rw [h.sr_eq ho]; exact h.safe_sc hn

theorem below_safe {k : Nat} (hk : k ≤ 3448) : Safe P (below P.B k) :=
  ⟨h.safe_low.1.sub_right (h.low_of hk), h.safe_low.2.sub_right (h.low_of hk)⟩

theorem sp_toNat : 3448 ≤ P.B.toNat := h.ok.BC

end In

theorem St.cov_sr {σ s : State} (hs : S P σ s) {o n : Nat} (ho : o < 8448) (hn : o + n ≤ 8448) :
    Covers [sr P o n] s.wr := by
  rw [hs.1.sr_eq ho]; exact Covers.one (St.sc_w hs hn)

theorem St.cov_ro {σ s : State} (hs : S P σ s) {R : Region} (hR : R ∈ P.ro) : Covers [R] (s.rd ++ s.wr) :=
  Covers.one (a := R.base) (n := R.len) ⟨R, hs.2.inRo hR, Region.contains_self _ _⟩

/-- A call writes only parts of `scratch` and the stack below the frame. -/
theorem Base.call {σ s t : State} (h : Base P σ s) {ws : List Region} {k : Nat} (hk : k ≤ 3448)
    (hws : ∀ r ∈ ws, ∃ o n, o < 8448 ∧ o + n ≤ 8448 ∧ r = sr P o n)
    (rd : t.rd = s.rd) (wr : t.wr = s.wr) (sp : t.gpr .esp = s.gpr .esp)
    (hf : Frame (ws ++ [below (s.gpr .esp) k]) s.mem t.mem) : Base P σ t := by
  have hs := h.1
  rw [hs.2.sp] at hf
  have hsub : ∀ r ∈ ws ++ [below P.B k], ∃ R ∈ P.lay.W, Region.Sub r R := by
    intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨o, n, ho, hn, rfl⟩ := hws r hr
      exact ⟨P.SCR, by simp, hs.1.sr_sub ho hn⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨P.lay.LOW, by simp, hs.1.low_of hk⟩
  refine h.frame (hs.2.write hf hsub rd wr sp) hf fun r hr => ?_
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨o, n, ho, hn, rfl⟩ := hws r hr; exact hs.1.sr_safe ho hn
  · simp only [List.mem_singleton] at hr; subst hr; exact hs.1.below_safe hk

/-- Bytes of `scratch` the call does not write. -/
theorem keep_sr {σ s t : State} (hs : S P σ s) {ws : List Region} {k : Nat} (hk : k ≤ 3448)
    (hf : Frame (ws ++ [below (s.gpr .esp) k]) s.mem t.mem) {o n : Nat} (ho : o < 8448) (hn : o + n ≤ 8448)
    (hd : ∀ r ∈ ws, (sr P o n).Disjoint r) :
    Spec.Rsa.bytesAt t.mem (sr P o n).base n = Spec.Rsa.bytesAt s.mem (sr P o n).base n := by
  rw [hs.2.sp] at hf
  refine Proof.RsaPkcs1Sig.bytesAt_frame hf (fun r hr => ?_) (by omega)
  rcases List.mem_append.mp hr with hr | hr
  · exact hd r hr
  · simp only [List.mem_singleton] at hr; subst hr; exact (hs.1.below_sr hk ho hn).symm

/-- The bytes of a buffer we only read, through a call. -/
theorem keep_ro {σ s t : State} (hs : S P σ s) {ws : List Region} {k : Nat} (hk : k ≤ 3448)
    (hf : Frame (ws ++ [below (s.gpr .esp) k]) s.mem t.mem)
    (hws : ∀ r ∈ ws, ∃ o n, o < 8448 ∧ o + n ≤ 8448 ∧ r = sr P o n) {R : Region} (hR : R ∈ P.ro) :
    Spec.Rsa.bytesAt t.mem R.base R.len = Spec.Rsa.bytesAt s.mem R.base R.len := by
  rw [hs.2.sp] at hf
  refine Proof.RsaPkcs1Sig.bytesAt_frame hf (fun r hr => ?_)
    (by have := hs.1.ok.fits R (List.mem_append_left _ hR); omega)
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨o, n, ho, hn, rfl⟩ := hws r hr; exact (hs.1.sr_ro ho hn hR).symm
  · simp only [List.mem_singleton] at hr; subst hr; exact (hs.1.below_ro hk hR).symm

/-- A SHA-256 state kept while memory changes elsewhere. -/
theorem repr_keep {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, 96⟩ r) {msg : List Byte} (h : Spec.Sha256.Repr m p msg) :
    Spec.Sha256.Repr m' p msg :=
  Proof.Hmac.Generic.Common.sha256_repr _ _ _ _ _ (fun i hi => hf.bytes (R := ⟨p, 96⟩) hd (by show (96 : Nat) ≤ 2 ^ 64; decide) hi) h

/-- A SHA-256 state in `scratch` through a call that does not write it. -/
theorem repr_keep_sr {σ s t : State} (hs : S P σ s) {ws : List Region} {k : Nat} (hk : k ≤ 3448)
    (hf : Frame (ws ++ [below (s.gpr .esp) k]) s.mem t.mem) {o : Nat} (ho : o + 96 ≤ 8448)
    (hd : ∀ r ∈ ws, (sr P o 96).Disjoint r) {msg : List Byte}
    (h : Spec.Sha256.Repr s.mem (sr P o 96).base msg) : Spec.Sha256.Repr t.mem (sr P o 96).base msg := by
  rw [hs.2.sp] at hf
  refine repr_keep hf (fun r hr => ?_) h
  rcases List.mem_append.mp hr with hr | hr
  · exact hd r hr
  · simp only [List.mem_singleton] at hr; subst hr; exact (hs.1.below_sr hk (by omega) ho).symm

/-! ## What a call leaves -/

/-- After a call that writes the regions `ws` and the `k` bytes below `esp`. -/
structure Called (s t : State) (ws : List Region) (k : Nat) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.gpr .esp = s.gpr .esp
  frame : Frame (ws ++ [below (s.gpr .esp) k]) s.mem t.mem

theorem Called.ofStream {s t : State} {ws : List Region} (a : Proof.Pbkdf2.Stream.X86.After s ws t) :
    Called s t ws 48 := ⟨a.rd, a.wr, a.esp, a.frame⟩

theorem Called.ofWhole {s t : State} {ws : List Region} (a : Proof.Pbkdf2.Whole.X86.After s ws t) :
    Called s t ws 76 := ⟨a.rd, a.wr, a.esp, a.frame⟩

/-- The regions a call writes, in `scratch`. -/
def InScr (P : EP) (ws : List Region) : Prop := ∀ r ∈ ws, ∃ o n, o < 8448 ∧ o + n ≤ 8448 ∧ r = sr P o n

theorem Called.base {σ s t : State} {ws : List Region} {k : Nat} (c : Called s t ws k) (h : Base P σ s)
    (hk : k ≤ 3448) (hws : InScr P ws) : Base P σ t :=
  h.call hk hws c.rd c.wr c.sp c.frame

theorem Called.st {σ s t : State} {ws : List Region} {k : Nat} (c : Called s t ws k) (hs : S P σ s)
    (hk : k ≤ 3448) (hws : InScr P ws) : S P σ t := by
  have hf := c.frame
  rw [hs.2.sp] at hf
  refine ⟨hs.1, hs.2.write hf (fun r hr => ?_) c.rd c.wr c.sp⟩
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨o, n, ho, hn, rfl⟩ := hws r hr
    exact ⟨P.SCR, by simp, hs.1.sr_sub ho hn⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨P.lay.LOW, by simp, hs.1.low_of hk⟩

theorem Called.keep {σ s t : State} {ws : List Region} {k : Nat} (c : Called s t ws k) (hs : S P σ s)
    (hk : k ≤ 3448) {o n : Nat} (ho : o < 8448) (hn : o + n ≤ 8448) (hd : ∀ r ∈ ws, (sr P o n).Disjoint r) :
    Spec.Rsa.bytesAt t.mem (sr P o n).base n = Spec.Rsa.bytesAt s.mem (sr P o n).base n :=
  keep_sr hs hk c.frame ho hn hd

theorem Called.keepRo {σ s t : State} {ws : List Region} {k : Nat} (c : Called s t ws k) (hs : S P σ s)
    (hk : k ≤ 3448) (hws : InScr P ws) {R : Region} (hR : R ∈ P.ro) :
    Spec.Rsa.bytesAt t.mem R.base R.len = Spec.Rsa.bytesAt s.mem R.base R.len :=
  keep_ro hs hk c.frame hws hR

theorem Called.repr {σ s t : State} {ws : List Region} {k : Nat} (c : Called s t ws k) (hs : S P σ s)
    (hk : k ≤ 3448) {o : Nat} (ho : o + 96 ≤ 8448) (hd : ∀ r ∈ ws, (sr P o 96).Disjoint r) {msg : List Byte}
    (h : Spec.Sha256.Repr s.mem (sr P o 96).base msg) : Spec.Sha256.Repr t.mem (sr P o 96).base msg :=
  repr_keep_sr hs hk c.frame ho hd h

/-! ## The arguments of the calls -/

section Args

variable {σ s : State} (hs : S P σ s) (v : Backend)
include hs

theorem stk48 : Proof.Pbkdf2.Stream.X86.stk s = below P.B 48 := by
  show below (s.gpr .esp) 48 = _; rw [hs.2.sp]

theorem stk76 : Proof.Pbkdf2.Whole.X86.stk s = below P.B 76 := by
  show below (s.gpr .esp) 76 = _; rw [hs.2.sp]

/-- SHA-256's `init` of the state at `scratch + sSt`. -/
theorem initA (he : s.gpr .edi = P.scr + BitVec.ofNat 32 sSt) :
    InitArgs (H := v.F.H) s .edi (P.scr + BitVec.ofNat 32 sSt) :=
  { hst := he, hr := by decide
    sp48 := by rw [hs.2.sp]; exact Nat.le_trans (by decide) hs.1.sp_toNat
    cw := St.cov_sr hs (o := sSt) (n := 96) (by decide) (by decide)
    b_st := by rw [stk48 hs]; exact hs.1.below_sr (o := sSt) (n := 96) (by decide) (by decide) (by decide)
    nst := hs.1.sr_fit (o := sSt) (n := 96) (by decide) (by decide) }

/-- SHA-256's `update` of the state at `scratch + sSt`, at the count `c`,
with `len` bytes at `d`. -/
theorem updA {d c : BitVec 32} {len : Nat} (edi : s.gpr .edi = P.scr + BitVec.ofNat 32 sSt)
    (esi : s.gpr .esi = c) (eax : s.gpr .eax = 0) (ecx : s.gpr .ecx = BitVec.ofNat 32 len)
    (edx : s.gpr .edx = d) (ebp : s.gpr .ebp = P.scr + BitVec.ofNat 32 sW) (hlen : len < 2 ^ 32)
    (cd : Covers [⟨d.setWidth 64, len⟩] (s.rd ++ s.wr))
    (d_st : Region.Disjoint ⟨d.setWidth 64, len⟩ (sr P sSt 96))
    (d_sc : Region.Disjoint ⟨d.setWidth 64, len⟩ (sr P sW 160))
    (b_d : (below P.B 48).Disjoint ⟨d.setWidth 64, len⟩) (nd : d.toNat + len ≤ 2 ^ 32) :
    UpdArgs (hk v) s .esi .edi (P.scr + BitVec.ofNat 32 sSt) d (P.scr + BitVec.ofNat 32 sW) c len :=
  { hst := edi, hlo := esi, eax := eax, ecx := ecx, edx := edx, ebp := ebp, hr := by decide, hl := by decide
    hlen := hlen
    sp48 := by rw [hs.2.sp]; exact Nat.le_trans (by decide) hs.1.sp_toNat
    cd := cd
    cw := Covers.cons (St.cov_sr hs (o := sSt) (n := 96) (by decide) (by decide))
      (St.cov_sr hs (o := sW) (n := 160) (by decide) (by decide))
    st_sc := hs.1.sr_sep (o := sSt) (n := 96) (o' := sW) (n' := 160) (by decide) (by decide) (by decide)
      (by decide) (by decide)
    d_st := d_st, d_sc := d_sc
    b_st := by rw [stk48 hs]; exact hs.1.below_sr (o := sSt) (n := 96) (by decide) (by decide) (by decide)
    b_d := by rw [stk48 hs]; exact b_d
    b_sc := by rw [stk48 hs]; exact hs.1.below_sr (o := sW) (n := 160) (by decide) (by decide) (by decide)
    nst := hs.1.sr_fit (o := sSt) (n := 96) (by decide) (by decide)
    nd := nd
    nsc := hs.1.sr_fit (o := sW) (n := 160) (by decide) (by decide) }

/-- SHA-256's `finalize` of the state at `scratch + sSt` to `scratch + t`. -/
theorem finA {t : Nat} {lo hi : BitVec 32} (ht₁ : 192 ≤ t) (ht₂ : t + 32 ≤ 2576)
    (edi : s.gpr .edi = P.scr + BitVec.ofNat 32 sSt) (eax : s.gpr .eax = lo) (ecx : s.gpr .ecx = hi)
    (edx : s.gpr .edx = P.scr + BitVec.ofNat 32 t) (ebp : s.gpr .ebp = P.scr + BitVec.ofNat 32 sW) :
    FinArgs (hk v) s .edi (P.scr + BitVec.ofNat 32 sSt) (P.scr + BitVec.ofNat 32 t)
      (P.scr + BitVec.ofNat 32 sW) lo hi :=
  { hst := edi, eax := eax, ecx := ecx, edx := edx, ebp := ebp, hr := by decide
    sp48 := by rw [hs.2.sp]; exact Nat.le_trans (by decide) hs.1.sp_toNat
    cw := Covers.cons (St.cov_sr hs (o := sSt) (n := 96) (by decide) (by decide))
      (Covers.cons (St.cov_sr hs (o := t) (n := 32) (by omega) (by omega))
        (St.cov_sr hs (o := sW) (n := 160) (by decide) (by decide)))
    st_o := hs.1.sr_sep (o := sSt) (n := 96) (o' := t) (n' := 32) (by simp only [sSt]; omega) (by decide)
      (by omega) (by decide) (by omega)
    st_sc := hs.1.sr_sep (o := sSt) (n := 96) (o' := sW) (n' := 160) (by decide) (by decide) (by decide)
      (by decide) (by decide)
    o_sc := hs.1.sr_sep (o := t) (n := 32) (o' := sW) (n' := 160) (by simp only [sW]; omega) (by omega)
      (by decide) (by omega) (by decide)
    b_st := by rw [stk48 hs]; exact hs.1.below_sr (o := sSt) (n := 96) (by decide) (by decide) (by decide)
    b_o := by rw [stk48 hs]; exact hs.1.below_sr (o := t) (n := 32) (by decide) (by omega) (by omega)
    b_sc := by rw [stk48 hs]; exact hs.1.below_sr (o := sW) (n := 160) (by decide) (by decide) (by decide)
    nst := hs.1.sr_fit (o := sSt) (n := 96) (by decide) (by decide)
    no := hs.1.sr_fit (o := t) (n := 32) (by omega) (by omega)
    nsc := hs.1.sr_fit (o := sW) (n := 160) (by decide) (by decide) }

/-- HMAC's `init` of the states at `scratch + sSt` and `scratch + sOuter`
with the `kl` bytes of key at `scratch + o`. -/
theorem hiA {o kl : Nat} (ho₁ : 192 ≤ o) (ho₂ : o + kl ≤ 2576) (hkl : kl ≤ 64)
    (edi : s.gpr .edi = P.scr + BitVec.ofNat 32 sSt) (esi : s.gpr .esi = P.scr + BitVec.ofNat 32 sOuter)
    (edx : s.gpr .edx = P.scr + BitVec.ofNat 32 o) (ecx : s.gpr .ecx = BitVec.ofNat 32 kl)
    (ebp : s.gpr .ebp = P.scr + BitVec.ofNat 32 sW) :
    HiArgs (hk v).SH 104 s (P.scr + BitVec.ofNat 32 sSt) (P.scr + BitVec.ofNat 32 sOuter)
      (P.scr + BitVec.ofNat 32 o) (P.scr + BitVec.ofNat 32 sW) kl :=
  { edi := edi, esi := esi, edx := edx, ecx := ecx, ebp := ebp
    klB := hkl
    kl32 := by omega
    sp := by rw [hs.2.sp]; exact Nat.le_trans (by decide) hs.1.sp_toNat
    cr := Covers.right (St.cov_sr hs (o := o) (n := kl) (by omega) (by omega))
    cw := Covers.cons (St.cov_sr hs (o := sSt) (n := 96) (by decide) (by decide))
      (Covers.cons (St.cov_sr hs (o := sOuter) (n := 96) (by decide) (by decide))
        (St.cov_sr hs (o := sW) (n := 104 * 8) (by decide) (by decide)))
    i_o := hs.1.sr_sep (o := sSt) (n := 96) (o' := sOuter) (n' := 96) (by decide) (by decide) (by decide)
      (by decide) (by decide)
    i_k := hs.1.sr_sep (o := sSt) (n := 96) (o' := o) (n' := kl) (by simp only [sSt]; omega) (by decide)
      (by omega) (by decide) (by omega)
    i_s := hs.1.sr_sep (o := sSt) (n := 96) (o' := sW) (n' := 104 * 8) (by decide) (by decide) (by decide)
      (by decide) (by decide)
    o_k := hs.1.sr_sep (o := sOuter) (n := 96) (o' := o) (n' := kl) (by simp only [sOuter]; omega) (by decide)
      (by omega) (by decide) (by omega)
    o_s := hs.1.sr_sep (o := sOuter) (n := 96) (o' := sW) (n' := 104 * 8) (by decide) (by decide) (by decide)
      (by decide) (by decide)
    k_s := hs.1.sr_sep (o := o) (n := kl) (o' := sW) (n' := 104 * 8) (by simp only [sW]; omega) (by omega)
      (by decide) (by omega) (by decide)
    b_i := by rw [stk76 hs]; exact hs.1.below_sr (o := sSt) (n := 96) (by decide) (by decide) (by decide)
    b_o := by rw [stk76 hs]; exact hs.1.below_sr (o := sOuter) (n := 96) (by decide) (by decide) (by decide)
    b_k := by rw [stk76 hs]; exact hs.1.below_sr (o := o) (n := kl) (by decide) (by omega) (by omega)
    b_s := by rw [stk76 hs]; exact hs.1.below_sr (o := sW) (n := 104 * 8) (by decide) (by decide) (by decide)
    ni := hs.1.sr_fit (o := sSt) (n := 96) (by decide) (by decide)
    no := hs.1.sr_fit (o := sOuter) (n := 96) (by decide) (by decide)
    nk := hs.1.sr_fit (o := o) (n := kl) (by omega) (by omega)
    nsc := hs.1.sr_fit (o := sW) (n := 104 * 8) (by decide) (by decide) }

/-- HMAC's `finalize` of the states at `scratch + sSt` and
`scratch + sOuter`, at the count `hi ++ lo`, to `scratch + t`. -/
theorem hfA {t : Nat} {lo hi : BitVec 32} (ht₁ : 192 ≤ t) (ht₂ : t + 32 ≤ 2576)
    (edx : s.gpr .edx = P.scr + BitVec.ofNat 32 sSt) (esi : s.gpr .esi = P.scr + BitVec.ofNat 32 sOuter)
    (eax : s.gpr .eax = lo) (ecx : s.gpr .ecx = hi) (edi : s.gpr .edi = P.scr + BitVec.ofNat 32 t)
    (ebp : s.gpr .ebp = P.scr + BitVec.ofNat 32 sW) :
    HfArgs (hk v).SH 104 s (P.scr + BitVec.ofNat 32 sSt) (P.scr + BitVec.ofNat 32 sOuter) lo hi
      (P.scr + BitVec.ofNat 32 t) (P.scr + BitVec.ofNat 32 sW) :=
  { edx := edx, esi := esi, eax := eax, ecx := ecx, edi := edi, ebp := ebp
    sp := by rw [hs.2.sp]; exact Nat.le_trans (by decide) hs.1.sp_toNat
    cr := Covers.right (St.cov_sr hs (o := sOuter) (n := 96) (by decide) (by decide))
    cw := Covers.cons (St.cov_sr hs (o := sSt) (n := 96) (by decide) (by decide))
      (Covers.cons (St.cov_sr hs (o := t) (n := 32) (by omega) (by omega))
        (St.cov_sr hs (o := sW) (n := 104 * 8) (by decide) (by decide)))
    i_u := hs.1.sr_sep (o := sSt) (n := 96) (o' := sOuter) (n' := 96) (by decide) (by decide) (by decide)
      (by decide) (by decide)
    i_o := hs.1.sr_sep (o := sSt) (n := 96) (o' := t) (n' := 32) (by simp only [sSt]; omega) (by decide)
      (by omega) (by decide) (by omega)
    i_s := hs.1.sr_sep (o := sSt) (n := 96) (o' := sW) (n' := 104 * 8) (by decide) (by decide) (by decide)
      (by decide) (by decide)
    u_o := hs.1.sr_sep (o := sOuter) (n := 96) (o' := t) (n' := 32) (by simp only [sOuter]; omega) (by decide)
      (by omega) (by decide) (by omega)
    u_s := hs.1.sr_sep (o := sOuter) (n := 96) (o' := sW) (n' := 104 * 8) (by decide) (by decide) (by decide)
      (by decide) (by decide)
    o_s := hs.1.sr_sep (o := t) (n := 32) (o' := sW) (n' := 104 * 8) (by simp only [sW]; omega) (by omega)
      (by decide) (by omega) (by decide)
    b_i := by rw [stk76 hs]; exact hs.1.below_sr (o := sSt) (n := 96) (by decide) (by decide) (by decide)
    b_u := by rw [stk76 hs]; exact hs.1.below_sr (o := sOuter) (n := 96) (by decide) (by decide) (by decide)
    b_o := by rw [stk76 hs]; exact hs.1.below_sr (o := t) (n := 32) (by decide) (by omega) (by omega)
    b_s := by rw [stk76 hs]; exact hs.1.below_sr (o := sW) (n := 104 * 8) (by decide) (by decide) (by decide)
    ni := hs.1.sr_fit (o := sSt) (n := 96) (by decide) (by decide)
    nu := hs.1.sr_fit (o := sOuter) (n := 96) (by decide) (by decide)
    no := hs.1.sr_fit (o := t) (n := 32) (by omega) (by omega)
    nsc := hs.1.sr_fit (o := sW) (n := 104 * 8) (by decide) (by decide) }

end Args

end VG.Proof.RsaPkcs1Enc.X86.Dec
