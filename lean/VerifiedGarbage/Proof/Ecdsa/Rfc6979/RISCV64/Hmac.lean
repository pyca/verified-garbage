module

-- separate module: its proofs cost more than its imports, and its importer's changes need
-- not re-check them

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.Common
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.ICall
import VerifiedGarbage.Proof.Framework.RISCV64.Syms
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Common
import VerifiedGarbage.Proof.Sha256.Stream

/-!
# Deterministic ECDSA on RISC-V: one HMAC, through the table

`HMAC_K(parts)` (`Cfg.hmac`), for the key `K` at the frame's `K` and a
message in parts, each in the frame after the save area or the private key
`d` (`PartOk`), of a length `D` plus a constant or a constant (`plen`),
written to the frame at `dst`: HMAC's `init` with `K` (`initArgs_ok`,
`init_ok`), the streaming `update` on the inner state with each part
(`updArgs_ok`, `updc_ok`, `upds_ok`), and HMAC's `finalize` (`finArgs_ok`,
`fin_ok`), each through the table (`tcall_ok`: the table's word, the
address of the function `TabOK` says the call reaches). Until `finalize`,
memory changes only in the states (in `scratch`) and the stack below the
frame (`St`), so the key and the parts are those at the start; `hmac_ok`
composes the pieces, which the proof of constant time relates one by one.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.RISCV64

open VG.RISCV64
open VG.RISCV64.Steps (Upd Mupd wp_mv wp_addi wp_li wp_add wp_ld)
open VG.Impl.Ecdsa.Rfc6979.RISCV64
open VG.Impl.Hmac.Stream.RISCV64 (Hash mov)
open VG.Proof.Hmac.Stream.RISCV64 (HashOK)
open VG.Proof.HmacTable.RISCV64 (HVar TabOK TabMem)
open VG.Proof.Hmac.Common (bytesAt_length xorPad_length)
open Spec.Hmac (xorPad ipad opad blockKey hmacBlockKey)
open Spec.Sha256 (bytesAt)

/-- Reads registers through register writes (`Upd`), deciding which register
each writes. -/
macro "upd_simp" " [" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  (set_option linter.unusedSimpArgs false in simp (disch := decide) only [$ls,*]))

/-! ## Lengths and parts -/

/-- A length's value. -/
abbrev lval (P : Rfc) (l : Len) : Nat := (if l.1 then P.H.D else 0) + l.2

/-- A part's length. -/
abbrev plen (P : Rfc) (p : Part) : Nat := lval P p.2.2

/-- What a part's base register holds. -/
def regV (s₀ : State) : Reg → Addr
  | .s1 => s₀.sp
  | .s3 => dk s₀
  | _ => 0

/-- Where a part is. -/
def pA (s₀ : State) (p : Part) : Addr := regV s₀ p.1 + BitVec.ofNat 64 p.2.1

/-- A part in the frame after the save area, or a prefix of `d`. -/
def PartOk (P : Rfc) (p : Part) : Prop :=
  ((p.1 = .s1 ∧ 96 ≤ p.2.1 ∧ p.2.1 + plen P p ≤ frB) ∨ (p.1 = .s3 ∧ p.2.1 = 0 ∧ plen P p ≤ P.Q)) ∧
    p.2.2.2 < 2048

theorem PartOk.len {P : Rfc} {p : Part} (h : PartOk P p) : plen P p ≤ 512 := by
  have := (sizes P).Q
  have : frB = 512 := rfl
  rcases h.1 with ⟨-, h₁, h₂⟩ | ⟨-, -, h₂⟩ <;> omega

theorem PartOk.off {P : Rfc} {p : Part} (h : PartOk P p) : p.2.1 < 2048 := by
  rcases h.1 with ⟨-, -, h₂⟩ | ⟨-, h₂, -⟩
  · have : frB = 512 := rfl; omega
  · omega

theorem PartOk.reg {P : Rfc} {p : Part} (h : PartOk P p) : p.1 = .s1 ∨ p.1 = .s3 := by
  rcases h.1 with ⟨h', -⟩ | ⟨h', -⟩ <;> simp [h']

/-- The message. -/
def msgOf (P : Rfc) (m : Mem) (s₀ : State) : List Part → List Byte
  | [] => []
  | p :: ps => bytesAt m (pA s₀ p) (plen P p) ++ msgOf P m s₀ ps

/-- The parts' lengths. -/
def tlen (P : Rfc) : List Part → Nat
  | [] => 0
  | p :: ps => plen P p + tlen P ps

theorem msgOf_length (P : Rfc) (m : Mem) (s₀ : State) : ∀ ps, (msgOf P m s₀ ps).length = tlen P ps
  | [] => rfl
  | p :: ps => by simp only [msgOf, List.length_append, bytesAt_length, msgOf_length P m s₀ ps, tlen]

/-- At most one part's length has `D`, after a count `c`. -/
def OneD : Len → List Part → Prop
  | _, [] => True
  | c, p :: ps => (c.1 && p.2.2.1) = false ∧ OneD (c.1 || p.2.2.1, c.2 + p.2.2.2) ps

theorem lval_add (P : Rfc) {c : Len} {p : Part} (h : (c.1 && p.2.2.1) = false) :
    lval P (c.1 || p.2.2.1, c.2 + p.2.2.2) = lval P c + plen P p := by
  obtain ⟨a, n⟩ := c
  obtain ⟨_, _, b, k⟩ := p
  cases a <;> cases b <;> simp_all [lval, plen] <;> omega

/-- The states' region in `scratch`. -/
abbrev stR (s₀ : State) : Region := cR s₀ 0 384

/-- The key's bytes. -/
abbrev kOf (P : Rfc) (s₀ : State) (m : Mem) : List Byte := bytesAt m (sA s₀ fK) P.H.D

/-- The key's block, for HMAC's pads. -/
abbrev k0Of (P : Rfc) (s₀ : State) (m : Mem) : List Byte := blockKey P.hH.SH.H (kOf P s₀ m)

theorem blockKey_length (P : Rfc) (k : List Byte) : (blockKey P.hH.SH.H k).length = P.H.B := by
  have hB := P.hH.hB
  have hDB : P.H.D ≤ P.H.B := by have := (sizes P).D; rcases P.hH.hB64 with h | h <;> omega
  simp only [blockKey, hB, List.length_append, List.length_replicate]
  split
  · rw [P.hH.hashLen]; omega
  · omega

/-! ## What holds between the calls -/

/-- From the start `s` of an HMAC: `KR`, and memory changed only in the
states and the stack below the frame. -/
structure St (P : Rfc) (s₀ s t : State) : Prop where
  kr : KR P s₀ t
  fr : Frame [stR s₀, stk P s₀] s.mem t.mem
  pr : ∀ r ∈ preserved, t.gpr r = s.gpr r

section
variable {P : Rfc} {s₀ : State} (hp : Pre P s₀)
include hp

/-- Regions of the frame are apart from what the calls of an HMAC write. -/
theorem fr_apart {o n : Nat} (h : o + n ≤ frB) : ∀ r ∈ [stR s₀, stk P s₀], Region.Disjoint (sR s₀ o n) r := by
  have sub : Region.Sub (sR s₀ o n) (frR s₀) := part_sub h
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact (hp.f_c.sub_left sub).sub_right (scr_sub (by omega))
  · exact (f_s hp).sub_left sub

theorem d_apart {n : Nat} (h : n ≤ P.Q) : ∀ r ∈ [stR s₀, stk P s₀], Region.Disjoint ⟨dk s₀, n⟩ r := by
  have sub : Region.Sub ⟨dk s₀, n⟩ (dR P s₀) := Region.sub_prefix h
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact (hp.d_c.sub_left sub).sub_right (scr_sub (by omega))
  · exact (hp.b_d.symm.sub_left sub)

theorem PartOk.apart {p : Part} (h : PartOk P p) :
    ∀ r ∈ [stR s₀, stk P s₀], Region.Disjoint ⟨pA s₀ p, plen P p⟩ r := by
  obtain ⟨r, o, l⟩ := p
  rcases h.1 with ⟨h₀, h₁, h₂⟩ | ⟨h₀, h₁, h₂⟩ <;> simp only at h₀ h₁ <;> subst h₀
  · exact fr_apart hp (o := o) h₂
  · subst h₁
    simp only [pA, regV, BitVec.add_zero]
    exact d_apart hp h₂

omit hp in
/-- The bytes of a region apart from the states and the stack below the
frame are those at the start. -/
theorem St.bytes {s t : State} (h : St P s₀ s t) {a : Addr} {n : Nat}
    (hd : ∀ r ∈ [stR s₀, stk P s₀], Region.Disjoint ⟨a, n⟩ r) (hn : n ≤ 2 ^ 64) :
    bytesAt t.mem a n = bytesAt s.mem a n :=
  Proof.Sha256.Stream.bytesAt_congr fun _ hi => h.fr.bytes (R := ⟨a, n⟩) hd hn hi

theorem St.key {s t : State} (h : St P s₀ s t) : kOf P s₀ t.mem = kOf P s₀ s.mem :=
  h.bytes (fr_apart hp (by have := (sizes P).D; have : frB = 512 := rfl; simp only [fK]; omega)) (by have := (sizes P).D; omega)

theorem St.part {s t : State} (h : St P s₀ s t) {p : Part} (hp' : PartOk P p) :
    bytesAt t.mem (pA s₀ p) (plen P p) = bytesAt s.mem (pA s₀ p) (plen P p) :=
  h.bytes (hp'.apart hp) (by have := hp'.len; omega)

omit hp in
theorem St.refl {s : State} (h : KR P s₀ s) : St P s₀ s s := ⟨h, Frame.refl _ _, fun _ _ => rfl⟩

/-- A call that writes the states and the stack below the frame keeps `St`. -/
theorem St.call {s t t' : State} (h : St P s₀ s t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr)
    (hsp : t'.sp = t.sp) (hcs : ∀ r ∈ preserved, t'.gpr r = t.gpr r) {rs : List Region}
    (hf : Frame rs t.mem t'.mem) (hw : ∀ r ∈ rs, Region.Sub r (stR s₀) ∨ ∃ n, r = below s₀.sp n ∧ n ≤ P.X) :
    St P s₀ s t' := by
  refine ⟨h.kr.call hp hrd hwr hsp hcs hf fun r hr => ?_, h.fr.trans (hf.sub fun r hr => ?_),
    fun r hr => (hcs r hr).trans (h.pr r hr)⟩
  · rcases hw r hr with h' | h'
    · exact .inr (.inr (.inl (fun x hx => scr_sub (by omega) x (h' x hx))))
    · exact .inr (.inr (.inr h'))
  · rcases hw r hr with h' | ⟨n, rfl, hn⟩
    · exact ⟨_, by simp, h'⟩
    · exact ⟨_, by simp, below_stk hp hn⟩

omit hp in
theorem St.upd {s t t' : State} (h : St P s₀ s t) {d : Reg} (hd : d ∉ preserved) {v : BitVec 64}
    (u : Upd t t' d v) : St P s₀ s t' :=
  ⟨h.kr.upd (fun h' => hd (kregs_pres _ h')) u, by rw [u.mem]; exact h.fr,
    fun r hr => (u.other r fun e => hd (e ▸ hr)).trans (h.pr r hr)⟩

end

/-! ## The regions of the calls -/

section
variable {P : Rfc} {s₀ : State} (hp : Pre P s₀)
include hp

theorem cov_fr {s : State} (hk : KR P s₀ s) {o n : Nat} (h : o + n ≤ frB) :
    ∃ r' ∈ s.rd ++ s.wr, ∃ off, (sR s₀ o n).base = r'.base + BitVec.ofNat 64 off ∧ off + (sR s₀ o n).len ≤ r'.len :=
  ⟨frR s₀, List.mem_append_right _ (fr_wr hp hk.wr), o, rfl, h⟩

theorem covW_fr {s : State} (hk : KR P s₀ s) {o n : Nat} (h : o + n ≤ frB) :
    ∃ r' ∈ s.wr, ∃ off, (sR s₀ o n).base = r'.base + BitVec.ofNat 64 off ∧ off + (sR s₀ o n).len ≤ r'.len :=
  ⟨frR s₀, fr_wr hp hk.wr, o, rfl, h⟩

theorem cov_scr {s : State} (hk : KR P s₀ s) {o n : Nat} (h : o + n ≤ 8192) :
    ∃ r' ∈ s.rd ++ s.wr, ∃ off, (cR s₀ o n).base = r'.base + BitVec.ofNat 64 off ∧ off + (cR s₀ o n).len ≤ r'.len :=
  ⟨scrR s₀, List.mem_append_right _ (scr_wr hp hk.wr), o, rfl, h⟩

theorem covW_scr {s : State} (hk : KR P s₀ s) {o n : Nat} (h : o + n ≤ 8192) :
    ∃ r' ∈ s.wr, ∃ off, (cR s₀ o n).base = r'.base + BitVec.ofNat 64 off ∧ off + (cR s₀ o n).len ≤ r'.len :=
  ⟨scrR s₀, scr_wr hp hk.wr, o, rfl, h⟩

theorem cov_part {s : State} (hk : KR P s₀ s) {p : Part} (h : PartOk P p) :
    ∃ r' ∈ s.rd ++ s.wr, ∃ off, pA s₀ p = r'.base + BitVec.ofNat 64 off ∧ off + plen P p ≤ r'.len := by
  obtain ⟨r, o, l⟩ := p
  rcases h.1 with ⟨h₀, -, h₂⟩ | ⟨h₀, h₁, h₂⟩ <;> simp only at h₀ <;> subst h₀
  · exact cov_fr hp hk h₂
  · simp only at h₁; subst h₁
    exact ⟨dR P s₀, List.mem_append_left _ (by rw [hk.rd, hp.rd]; simp), 0, rfl, by simpa using h₂⟩

/-- The states, apart from each other. -/
theorem in_out : Region.Disjoint (cR s₀ sIn P.H.S) (cR s₀ sOut P.H.S) :=
  scr_disj hp (.inl (by have := (sizes P).S192; simp only [sIn, sOut]; omega)) (by have := (sizes P).S192; simp only [sIn]; omega)
    (by have := (sizes P).S192; simp only [sOut]; omega)

omit hp in
theorem st_in : Region.Sub (cR s₀ sIn P.H.S) (stR s₀) :=
  Offset.sub _ (by simp only [sIn]; omega) (by have := (sizes P).S192; simp only [sIn]; omega)

omit hp in
theorem st_out : Region.Sub (cR s₀ sOut P.H.S) (stR s₀) :=
  Offset.sub _ (by simp only [sOut]; omega) (by have := (sizes P).S192; simp only [sOut]; omega)

/-- A part of the frame is apart from the states. -/
theorem fr_st {o n : Nat} (h : o + n ≤ frB) {r : Region} (hr : Region.Sub r (stR s₀)) :
    Region.Disjoint (sR s₀ o n) r :=
  (hp.f_c.sub_left (part_sub h)).sub_right fun x hx => scr_sub (by omega) x (hr x hx)

/-- The stack below the stack pointer is apart from the states and the frame. -/
theorem below_st {s : State} (hk : KR P s₀ s) {n : Nat} (hn : n ≤ P.X) {r : Region} (hr : Region.Sub r (stR s₀)) :
    (below s.sp n).Disjoint r := by
  rw [hk.sp]
  exact (hp.b_c.sub_left (below_stk hp hn)).sub_right fun x hx => scr_sub (by omega) x (hr x hx)

theorem below_fr {s : State} (hk : KR P s₀ s) {n : Nat} (hn : n ≤ P.X) {o m : Nat} (h : o + m ≤ frB) :
    (below s.sp n).Disjoint (sR s₀ o m) := by
  rw [hk.sp]
  exact ((f_s hp).sub_left (part_sub h)).symm.sub_left (below_stk hp hn)

theorem below_part {s : State} (hk : KR P s₀ s) {n : Nat} (hn : n ≤ P.X) {p : Part} (h : PartOk P p) :
    (below s.sp n).Disjoint ⟨pA s₀ p, plen P p⟩ := by
  obtain ⟨r, o, l⟩ := p
  rcases h.1 with ⟨h₀, -, h₂⟩ | ⟨h₀, h₁, h₂⟩ <;> simp only at h₀ <;> subst h₀
  · exact below_fr hp hk hn h₂
  · simp only at h₁; subst h₁
    rw [hk.sp]
    simp only [pA, regV, BitVec.add_zero]
    exact (hp.b_d.sub_left (below_stk hp hn)).sub_right (Region.sub_prefix h₂)

theorem part_st {p : Part} (h : PartOk P p) {r : Region} (hr : Region.Sub r (stR s₀)) :
    Region.Disjoint ⟨pA s₀ p, plen P p⟩ r := by
  obtain ⟨q, o, l⟩ := p
  rcases h.1 with ⟨h₀, -, h₂⟩ | ⟨h₀, h₁, h₂⟩ <;> simp only at h₀ <;> subst h₀
  · exact fr_st hp h₂ hr
  · simp only at h₁; subst h₁
    simp only [pA, regV, BitVec.add_zero]
    exact (hp.d_c.sub_left (Region.sub_prefix h₂)).sub_right fun x hx => scr_sub (by omega) x (hr x hx)

end

/-! ## The calls through the table -/

section
variable {P : Rfc} {s₀ : State} (hp : Pre P s₀)
include hp

/-- The table's function `j`, among `ts`, which reaches `n`: the call of `n`
from the state the load of its address leaves. -/
theorem tcall_ok {t : State} (hk : KR P s₀ t) (hsy : t.syms = s₀.syms) {j : Nat} (hj : j < 3)
    {ts : List (String × Prog isa)} {n : String} {c : Prog isa}
    (hf : ts.find? (fun q => s₀.syms q.1 == s₀.syms n) = some (n, c))
    (hw : s₀.mem.readW (tab s₀ + BitVec.ofNat 64 (8 * j)) 64 = s₀.syms n) {Q : State → Prop}
    (kk : ∀ t', Upd t t' .t1 (s₀.syms n) → t'.syms = t.syms → WP isa (.call n c) t' Q) :
    WP isa (tcall j ts) t Q := by
  unfold tcall
  have hin : InRegions (t.rd ++ t.wr) (tab s₀ + BitVec.ofNat 64 (8 * j)) 8 :=
    ⟨tabR s₀, List.mem_append_left _ (by rw [hk.rd, hp.rd]; simp),
      Offset.contains_base _ (by omega) (by have := hp.nt; omega)⟩
  have hal : (tab s₀ + BitVec.ofNat 64 (8 * j)).toNat % 8 = 0 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := hp.ta; have := hp.nt; omega
  refine WP.seq (VG.RISCV64.WP.of_syms (wp_ld (by omega) (by rw [hk.s6]) hal hin fun t' u => WP.block_nil fun sy => ?_))
  have hv : t.mem.readW (tab s₀ + BitVec.ofNat 64 (8 * j)) 64 = s₀.syms n := by
    rw [hk.tabW hp (by omega), hw]
  rw [hv] at u
  refine WP.icalls_of_call (a := t'.gpr .t1) rfl ?_ (kk t' u sy)
  show ts.find? (fun q => t'.syms q.1 == t'.gpr .t1) = _
  rw [u.gpr, sy, hsy]; exact hf

end

/-! ## HMAC's `init` -/

/-- After `init`'s arguments. -/
def HI (P : Rfc) (s₀ s t : State) : Prop :=
  St P s₀ s t ∧ t.gpr .a0 = cA s₀ sIn ∧ t.gpr .a1 = cA s₀ sOut ∧ t.gpr .a2 = sA s₀ fK ∧
    t.gpr .a3 = BitVec.ofNat 64 P.H.D

/-- After `init`: the states of the key. -/
def HK (P : Rfc) (s₀ s t : State) : Prop :=
  St P s₀ s t ∧ P.hH.SH.Repr t.mem (cA s₀ sIn) (xorPad (k0Of P s₀ s.mem) ipad) ∧
    P.hH.SH.Repr t.mem (cA s₀ sOut) (xorPad (k0Of P s₀ s.mem) opad)

section
variable {P : Rfc} {s₀ : State} (hp : Pre P s₀)
include hp

omit hp in
theorem initArgs_ok {s : State} (h : KR P s₀ s) : WP isa (.block Cfg.initArgs) s (HI P s₀ s) := by
  unfold Cfg.initArgs
  refine wp_addi (by simp only [sIn]; omega) fun s₁ u₁ => wp_addi (by simp only [sOut]; omega) fun s₂ u₂ =>
    wp_addi (by simp only [fK]; omega) fun s₃ u₃ => wp_mv fun s₄ u₄ => WP.block_nil ?_
  have St₄ : St P s₀ s s₄ := ((((St.refl h).upd (by decide) u₁).upd (by decide) u₂).upd (by decide) u₃).upd
    (by decide) u₄
  refine ⟨St₄, ?_, ?_, ?_, ?_⟩
  · upd_simp [u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
    rw [h.s0]
  · upd_simp [u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
    rw [h.s0]
  · upd_simp [u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
    rw [h.s1]
  · upd_simp [u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
    exact h.s7

theorem hi_args {s t : State} (h : HI P s₀ s t) : HiArgs P t (cA s₀ sIn) (cA s₀ sOut) (sA s₀ fK) P.H.D := by
  obtain ⟨St, h0, h1, h2, h3⟩ := h
  have hz := sizes P
  have hX := hz.X
  have hk : fK + P.H.D ≤ frB := by have := hz.D; have : frB = 512 := rfl; simp only [fK]; omega
  refine ⟨h0, h1, h2, by rw [h3, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hz.D; omega)],
    by rw [St.kr.sp]; exact hp.al, by rw [St.kr.sp]; have := hp.spX; omega, in_out hp,
    fr_st hp hk ((st_in (P := P))), fr_st hp hk ((st_out (P := P))), below_st hp St.kr hX.1 ((st_in (P := P))),
    below_st hp St.kr hX.1 ((st_out (P := P))), below_fr hp St.kr hX.1 hk, ?_, ?_⟩
  · refine VG.Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact cov_fr hp St.kr hk
    · exact cov_scr hp St.kr (by have := hz.S192; simp only [sIn]; omega)
    · exact cov_scr hp St.kr (by have := hz.S192; simp only [sOut]; omega)
  · refine VG.Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact covW_scr hp St.kr (by have := hz.S192; simp only [sIn]; omega)
    · exact covW_scr hp St.kr (by have := hz.S192; simp only [sOut]; omega)

theorem init_ok {s t : State} (h : HI P s₀ s t) : WP isa (.call P.w.hiN P.H.init) t (HK P s₀ s) := by
  have hz := sizes P
  have hX := hz.X
  refine hi_call (hi_args hp h) fun t' a hI hO => ?_
  have St' : St P s₀ s t' := h.1.call hp a.rd a.wr a.sp a.cs a.frame fun r hr => by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl ((st_in (P := P)))
    · exact .inl ((st_out (P := P)))
    · exact .inr ⟨_, by rw [h.1.kr.sp], hX.1⟩
  have hk : bytesAt t.mem (sA s₀ fK) P.H.D = kOf P s₀ s.mem := h.1.key hp
  rw [hk] at hI hO
  exact ⟨St', hI, hO⟩

/-- HMAC's `init`, through the table. -/
theorem initT_ok {s t : State} (h : HI P s₀ s t) (hsy : t.syms = s₀.syms) :
    WP isa (tcall 0 P.c.f.init) t (HK P s₀ s) :=
  tcall_ok hp h.1.kr hsy (j := 0) (by decide) hp.tok.i (by rw [Nat.mul_zero, BitVec.add_zero]; exact hp.tmem.1)
    fun t' u _ => init_ok hp ⟨h.1.upd (by decide) u, by rw [u.other _ (by decide)]; exact h.2.1,
      by rw [u.other _ (by decide)]; exact h.2.2.1, by rw [u.other _ (by decide)]; exact h.2.2.2.1,
      by rw [u.other _ (by decide)]; exact h.2.2.2.2⟩

end

/-! ## The streaming `update` -/

/-- After the parts `pre` were absorbed. -/
def HU (P : Rfc) (s₀ s : State) (pre : List Byte) (t : State) : Prop :=
  St P s₀ s t ∧ P.hH.SH.Repr t.mem (cA s₀ sIn) (xorPad (k0Of P s₀ s.mem) ipad ++ pre) ∧
    P.hH.SH.Repr t.mem (cA s₀ sOut) (xorPad (k0Of P s₀ s.mem) opad)

/-- After `update`'s arguments for the part `p`. -/
def HUA (P : Rfc) (s₀ s : State) (pre : List Byte) (p : Part) (t : State) : Prop :=
  HU P s₀ s pre t ∧ t.gpr .a0 = cA s₀ sIn ∧ t.gpr .a1 = BitVec.ofNat 64 (P.H.B + pre.length) ∧
    t.gpr .a2 = pA s₀ p ∧ t.gpr .a3 = BitVec.ofNat 64 (plen P p)

/-- `d ← B + l`. -/
theorem cntTo_ok {P : Rfc} {s₀ s : State} (h : KR P s₀ s) {d : Reg} (hd : d ∉ kregs) {l : Len} (hl : l.2 < 2048)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Upd s s' d (BitVec.ofNat 64 (P.H.B + lval P l)) → WP isa (.block is) s' Q) :
    WP isa (.block (cntTo d l ++ is)) s Q := by
  obtain ⟨b, n⟩ := l
  have h7 := h.s7
  have h8 := h.s8
  have d7 : d ≠ .s7 := fun e => hd (by subst e; decide)
  have d8 : d ≠ .s8 := fun e => hd (by subst e; decide)
  cases b
  · refine wp_addi hl fun s₁ u₁ => k s₁ ?_
    rw [h8, BitVec.ofNat_add_ofNat] at u₁
    simpa [lval] using u₁
  · refine wp_add fun s₁ u₁ => wp_addi hl fun s₂ u₂ => k s₂ ?_
    refine ⟨?_, fun r hr => (u₂.other r hr).trans (u₁.other r hr), u₂.mem.trans u₁.mem, u₂.rd.trans u₁.rd,
      u₂.wr.trans u₁.wr, u₂.sp.trans u₁.sp⟩
    rw [u₂.gpr, u₁.gpr, h8, h7, BitVec.ofNat_add_ofNat, BitVec.ofNat_add_ofNat]
    simp only [lval, ↓reduceIte, Nat.add_assoc]

/-- `d ← l`. -/
theorem lenTo_ok {P : Rfc} {s₀ s : State} (h : KR P s₀ s) {d : Reg} {l : Len} (hl : l.2 < 2048)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Upd s s' d (BitVec.ofNat 64 (lval P l)) → WP isa (.block is) s' Q) :
    WP isa (.block (lenTo d l ++ is)) s Q := by
  obtain ⟨b, n⟩ := l
  cases b
  · exact wp_li hl fun s₁ u₁ => k s₁ (by simpa [lval] using u₁)
  · refine wp_addi hl fun s₁ u₁ => k s₁ ?_
    rw [h.s7, BitVec.ofNat_add_ofNat] at u₁
    simpa [lval] using u₁

section
variable {P : Rfc} {s₀ : State} (hp : Pre P s₀)
include hp

omit hp in
theorem HK.hu {s t : State} (h : HK P s₀ s t) : HU P s₀ s [] t := by
  obtain ⟨a, b, c⟩ := h
  exact ⟨a, by rw [List.append_nil]; exact b, c⟩

omit hp in
theorem updArgs_ok {s t : State} {pre : List Byte} {cnt : Len} {p : Part} (h : HU P s₀ s pre t)
    (hc : lval P cnt = pre.length) (hr : p.1 = .s1 ∨ p.1 = .s3) (hc2 : cnt.2 < 2048) (ho : p.2.1 < 2048)
    (hl : p.2.2.2 < 2048) :
    WP isa (.block (Cfg.updArgs cnt p)) t (HUA P s₀ s pre p) := by
  obtain ⟨q, o, l⟩ := p
  simp only at hr ho hl
  have hq : t.gpr q = regV s₀ q := by rcases hr with rfl | rfl; exacts [h.1.kr.s1, h.1.kr.s3]
  have q0 : q ≠ .a0 := by rcases hr with rfl | rfl <;> decide
  have q1 : q ≠ .a1 := by rcases hr with rfl | rfl <;> decide
  unfold Cfg.updArgs
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  rw [← List.append_nil (lenTo .a3 l)]
  refine wp_addi (by simp only [sIn]; omega) fun s₁ u₁ => ?_
  have k₁ := h.1.kr.upd (by decide) u₁
  refine cntTo_ok k₁ (d := .a1) (by decide) hc2 fun s₂ u₂ => ?_
  have k₂ := k₁.upd (by decide) u₂
  refine wp_addi ho fun s₃ u₃ => ?_
  have k₃ := k₂.upd (by decide) u₃
  refine lenTo_ok k₃ (d := .a3) hl fun s₄ u₄ => WP.block_nil ?_
  have St₄ := ((((h.1).upd (by decide) u₁).upd (by decide) u₂).upd (by decide) u₃).upd (by decide) u₄
  have mm : s₄.mem = t.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine ⟨⟨St₄, by rw [mm]; exact h.2.1, by rw [mm]; exact h.2.2⟩, ?_, ?_, ?_, ?_⟩
  · upd_simp [u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
    rw [h.1.kr.s0]
  · upd_simp [u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
    rw [hc]
  · rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ q1, u₁.other _ q0, hq]; rfl
  · exact u₄.gpr

omit hp in
/-- `HUA` across the load of a table's word. -/
theorem HUA.upd {s t t₀ : State} {pre : List Byte} {p : Part} (h : HUA P s₀ s pre p t) {v : BitVec 64}
    (u : Upd t t₀ .t1 v) : HUA P s₀ s pre p t₀ := by
  obtain ⟨⟨hS₀, hi, ho⟩, h0, h1, h2, h3⟩ := h
  exact ⟨⟨hS₀.upd (by decide) u, by rw [u.mem]; exact hi, by rw [u.mem]; exact ho⟩,
    by rw [u.other _ (by decide)]; exact h0, by rw [u.other _ (by decide)]; exact h1,
    by rw [u.other _ (by decide)]; exact h2, by rw [u.other _ (by decide)]; exact h3⟩

/-- What `update` needs, after its arguments. -/
theorem upd_args {s t₀ : State} {pre : List Byte} {p : Part} (h : HUA P s₀ s pre p t₀) (hpo : PartOk P p) :
    UpdArgs P t₀ (cA s₀ sIn) (pA s₀ p) (plen P p) := by
  obtain ⟨⟨hS, -, -⟩, h0, -, h2, h3⟩ := h
  have hz := sizes P
  have hX := hz.X
  refine ⟨h0, h2, by rw [h3, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hpo.len; omega)],
    part_st hp hpo ((st_in (P := P))), by rw [hS.kr.sp]; exact hp.al,
    by rw [hS.kr.sp]; have := hp.spX; omega, below_st hp hS.kr hX.2.2.1 ((st_in (P := P))),
    below_part hp hS.kr hX.2.2.1 hpo, ?_, ?_⟩
  · refine VG.Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact cov_part hp hS.kr hpo
    · exact cov_scr hp hS.kr (by have := hz.S192; simp only [sIn]; omega)
  · refine VG.Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    exact covW_scr hp hS.kr (by have := hz.S192; simp only [sIn]; omega)

/-- The call of the streaming `update`, after its arguments. -/
theorem updcall_ok {s t₀ : State} {pre : List Byte} {p : Part} (h : HUA P s₀ s pre p t₀) (hpo : PartOk P p) :
    WP isa (.call P.H.updN P.H.updC) t₀ (HU P s₀ s (pre ++ bytesAt s.mem (pA s₀ p) (plen P p))) := by
  have ha := upd_args hp h hpo
  obtain ⟨⟨hS, hi, ho⟩, h0, h1, h2, h3⟩ := h
  have hz := sizes P
  have hX := hz.X
  refine upd_call ha fun t' a hu => ?_
  have St' : St P s₀ s t' := hS.call hp a.rd a.wr a.sp a.cs a.frame fun r hr => by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inl ((st_in (P := P)))
    · exact .inr ⟨_, by rw [hS.kr.sp], hX.2.2.1⟩
  have hK := blockKey_length P (kOf P s₀ s.mem)
  have e := hu _ hi (by rw [h1, List.length_append, xorPad_length, hK])
  rw [List.append_assoc, hS.part hp hpo] at e
  refine ⟨St', e, P.hH.congr t₀.mem t'.mem _ _ (fun i hi' => ?_) ho⟩
  refine a.frame.bytes (R := cR s₀ sOut P.H.S) (fun r hr => ?_) (by show P.H.S ≤ 2 ^ 64; have := hz.S192; omega) hi'
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact (in_out hp).symm
  · exact (below_st hp hS.kr hX.2.2.1 ((st_out (P := P)))).symm

/-- The streaming `update`, through the table, with the part `p`. -/
theorem updc_ok {s t : State} {pre : List Byte} {p : Part} (h : HUA P s₀ s pre p t) (hpo : PartOk P p)
    (hsy : t.syms = s₀.syms) :
    WP isa (tcall 1 P.c.f.upd) t (HU P s₀ s (pre ++ bytesAt s.mem (pA s₀ p) (plen P p))) :=
  tcall_ok hp h.1.1.kr hsy (j := 1) (by decide) hp.tok.u (by rw [Nat.mul_one]; exact hp.tmem.2.1)
    fun _ u _ => updcall_ok hp (h.upd u) hpo

/-- The parts absorbed, one `update` each. -/
theorem upds_ok {s : State} : ∀ (ps : List Part) {t : State} {pre : List Byte} {cnt : Len}, HU P s₀ s pre t →
    t.syms = s₀.syms → lval P cnt = pre.length → OneD cnt ps → (∀ p ∈ ps, PartOk P p) →
    cnt.2 + (ps.map (·.2.2.2)).sum < 2048 →
    WP isa (P.c.upds cnt ps) t (HU P s₀ s (pre ++ msgOf P s.mem s₀ ps))
  | [], t, pre, cnt, h, _, _, _, _, _ => WP.block_nil (by rw [msgOf, List.append_nil]; exact h)
  | p :: ps, t, pre, cnt, h, hsy, hc, ho, hps, hb => by
    have hpo : PartOk P p := hps p (by simp)
    simp only [List.map_cons, List.sum_cons] at hb
    unfold Cfg.upds
    refine WP.seq (VG.RISCV64.WP.mono_syms (WP.seq (VG.RISCV64.WP.mono_syms (updArgs_ok h hc hpo.reg (by omega) hpo.off (by omega))
      fun t₁ h₁ y₁ => updc_ok hp h₁ hpo (y₁.trans hsy))) fun t₂ h₂ y₂ => ?_)
    refine WP.mono (upds_ok ps h₂ (y₂.trans hsy) (by rw [lval_add P ho.1, List.length_append, bytesAt_length, hc])
      ho.2 (fun q hq => hps q (by simp [hq])) (by omega)) fun t₃ h₃ => ?_
    rwa [List.append_assoc, ← msgOf.eq_2] at h₃

end

/-! ## HMAC's `finalize` -/

/-- After `finalize`'s arguments, for the message `msg` and the MAC to `dst`. -/
def HFA (P : Rfc) (s₀ s : State) (msg : List Byte) (dst : Nat) (t : State) : Prop :=
  HU P s₀ s msg t ∧ t.gpr .a0 = cA s₀ sIn ∧ t.gpr .a1 = cA s₀ sOut ∧
    t.gpr .a2 = BitVec.ofNat 64 (P.H.B + msg.length) ∧ t.gpr .a3 = sA s₀ dst

/-- After an HMAC: the MAC at `dst`, and memory changed only in the states,
the MAC and the stack below the frame. -/
def HD (P : Rfc) (s₀ s : State) (msg : List Byte) (dst : Nat) (t : State) : Prop :=
  KR P s₀ t ∧ bytesAt t.mem (sA s₀ dst) P.H.D = Spec.Hmac.hmac P.hH.SH.H (kOf P s₀ s.mem) msg ∧
    Frame [stR s₀, sR s₀ dst P.H.D, stk P s₀] s.mem t.mem ∧ ∀ r ∈ preserved, t.gpr r = s.gpr r

section
variable {P : Rfc} {s₀ : State} (hp : Pre P s₀)
include hp

omit hp in
theorem finArgs_ok {s t : State} {msg : List Byte} {len : Len} (h : HU P s₀ s msg t) (hl : lval P len = msg.length)
    (hl2 : len.2 < 2048) (dst : Nat) (hd : dst < 2048) :
    WP isa (.block (Cfg.finArgs len dst)) t (HFA P s₀ s msg dst) := by
  unfold Cfg.finArgs
  simp only [List.cons_append, List.nil_append]
  refine wp_addi (by simp only [sIn]; omega) fun s₁ u₁ => wp_addi (by simp only [sOut]; omega) fun s₂ u₂ => ?_
  have k₂ := (h.1.kr.upd (by decide) u₁).upd (by decide) u₂
  refine cntTo_ok k₂ (d := .a2) (by decide) hl2 fun s₃ u₃ => wp_addi hd fun s₄ u₄ => WP.block_nil ?_
  have St₄ := ((((h.1).upd (by decide) u₁).upd (by decide) u₂).upd (by decide) u₃).upd (by decide) u₄
  have mm : s₄.mem = t.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine ⟨⟨St₄, by rw [mm]; exact h.2.1, by rw [mm]; exact h.2.2⟩, ?_, ?_, ?_, ?_⟩
  · upd_simp [u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
    rw [h.1.kr.s0]
  · upd_simp [u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
    rw [h.1.kr.s0]
  · upd_simp [u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
    rw [hl]
  · upd_simp [u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
    rw [h.1.kr.s1]

theorem hf_args {s t : State} {msg : List Byte} {dst : Nat} (hdst : 96 ≤ dst ∧ dst + P.H.D ≤ frB)
    (h : HFA P s₀ s msg dst t) : HfArgs P t (cA s₀ sIn) (cA s₀ sOut) (sA s₀ dst) := by
  obtain ⟨⟨St, -, -⟩, h0, h1, -, h3⟩ := h
  have hz := sizes P
  have hX := hz.X
  refine ⟨h0, h1, h3, by rw [St.kr.sp]; exact hp.al, by rw [St.kr.sp]; have := hp.spX; omega, in_out hp,
    (fr_st hp hdst.2 ((st_in (P := P)))).symm, (fr_st hp hdst.2 ((st_out (P := P)))).symm,
    below_st hp St.kr hX.2.1 ((st_in (P := P))), below_st hp St.kr hX.2.1 ((st_out (P := P))),
    below_fr hp St.kr hX.2.1 hdst.2, ?_, ?_⟩
  · refine VG.Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact cov_scr hp St.kr (by have := hz.S192; simp only [sOut]; omega)
    · exact cov_scr hp St.kr (by have := hz.S192; simp only [sIn]; omega)
    · exact cov_fr hp St.kr hdst.2
  · refine VG.Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact covW_scr hp St.kr (by have := hz.S192; simp only [sIn]; omega)
    · exact covW_fr hp St.kr hdst.2

theorem fin_ok {s t : State} {msg : List Byte} {dst : Nat} (hdst : 96 ≤ dst ∧ dst + P.H.D ≤ frB)
    (hm : P.H.B + msg.length < 2 ^ 63) (h : HFA P s₀ s msg dst t) :
    WP isa (.call P.w.hfN P.H.finalize) t (HD P s₀ s msg dst) := by
  have hz := sizes P
  have hX := hz.X
  have St := h.1.1
  refine hf_call (hf_args hp hdst h) fun t' a hf => ?_
  have hK := blockKey_length P (kOf P s₀ s.mem)
  refine ⟨St.kr.call hp a.rd a.wr a.sp a.cs a.frame fun r hr => ?_, ?_, ?_,
    fun r hr => (a.cs r hr).trans (St.pr r hr)⟩
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inr (.inr (.inl (scr_sub (by have := hz.S192; simp only [sIn]; omega))))
    · exact .inl ⟨_, _, rfl, hdst.1, hdst.2⟩
    · exact .inr (.inr (.inr ⟨_, by rw [St.kr.sp], hX.2.1⟩))
  · exact hf _ msg hK (by rw [hK]; omega) h.1.2.1 (by rw [h.2.2.2.1]) h.1.2.2
  · refine (St.fr.sub fun r hr => ?_).trans (a.frame.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨stR s₀, by simp, fun x hx => hx⟩
      · exact ⟨stk P s₀, by simp, fun x hx => hx⟩
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨stR s₀, by simp, (st_in (P := P))⟩
    · exact ⟨sR s₀ dst P.H.D, by simp, fun x hx => hx⟩
    · exact ⟨stk P s₀, by simp, by rw [St.kr.sp]; exact below_stk hp hX.2.1⟩

/-- HMAC's `finalize`, through the table. -/
theorem finT_ok {s t : State} {msg : List Byte} {dst : Nat} (hdst : 96 ≤ dst ∧ dst + P.H.D ≤ frB)
    (hm : P.H.B + msg.length < 2 ^ 63) (h : HFA P s₀ s msg dst t) (hsy : t.syms = s₀.syms) :
    WP isa (tcall 2 P.c.f.fin) t (HD P s₀ s msg dst) :=
  tcall_ok hp h.1.1.kr hsy (j := 2) (by decide) hp.tok.f hp.tmem.2.2
    fun t' u _ => (fin_ok hp hdst hm ⟨⟨h.1.1.upd (by decide) u, by rw [u.mem]; exact h.1.2.1,
      by rw [u.mem]; exact h.1.2.2⟩, by rw [u.other _ (by decide)]; exact h.2.1,
      by rw [u.other _ (by decide)]; exact h.2.2.1, by rw [u.other _ (by decide)]; exact h.2.2.2.1,
      by rw [u.other _ (by decide)]; exact h.2.2.2.2⟩).mono fun t'' ⟨a, b, c, d⟩ =>
        ⟨a, b, c, fun r hr => by
          rw [d r hr]⟩

/-- `HMAC_K(parts)` to `dst`. -/
theorem hmac_ok {s : State} (h : KR P s₀ s) (hsy : s.syms = s₀.syms) {ps : List Part}
    (hps : ∀ p ∈ ps, PartOk P p) (hone : OneD (false, 0) ps) (htot : lval P (total ps) = tlen P ps)
    (hb : (total ps).2 < 2048) (hb' : (ps.map (·.2.2.2)).sum < 2048) (htl : tlen P ps < 2048) {dst : Nat}
    (hdst : 96 ≤ dst ∧ dst + P.H.D ≤ frB) :
    WP isa (P.c.hmac ps dst) s (HD P s₀ s (msgOf P s.mem s₀ ps) dst) := by
  unfold Cfg.hmac
  refine WP.seq (VG.RISCV64.WP.mono_syms (initArgs_ok h) fun t₁ h₁ y₁ => ?_)
  refine WP.seq (VG.RISCV64.WP.mono_syms (initT_ok hp h₁ (y₁.trans hsy)) fun t₂ h₂ y₂ => ?_)
  refine WP.seq (VG.RISCV64.WP.mono_syms (upds_ok hp ps (pre := []) (cnt := (false, 0)) h₂.hu (y₂.trans (y₁.trans hsy))
    (by simp [lval]) hone hps (by simpa using hb')) fun t₃ h₃ y₃ => ?_)
  rw [List.nil_append] at h₃
  have hl := msgOf_length P s.mem s₀ ps
  refine WP.seq (VG.RISCV64.WP.mono_syms (finArgs_ok h₃ (len := total ps) (by rw [htot, hl]) hb dst
    (by have : frB = 512 := rfl; omega)) fun t₄ h₄ y₄ => ?_)
  have hz := (sizes P).B
  exact finT_ok hp hdst (by rw [hl]; rcases hz with h' | h' <;> rw [h'] <;> omega) h₄
    (y₄.trans (y₃.trans (y₂.trans (y₁.trans hsy))))

end

theorem add_ofNat_add' (p : Addr) (a b : Nat) :
    p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

theorem bytesAt_take (m : Mem) (p : Addr) {k n : Nat} (h : k ≤ n) : bytesAt m p k = (bytesAt m p n).take k := by
  rw [show n = k + (n - k) by omega, VG.Proof.Hmac.Common.bytesAt_add, List.take_left' (bytesAt_length _ _ _)]

end VG.Proof.Ecdsa.Rfc6979.RISCV64
