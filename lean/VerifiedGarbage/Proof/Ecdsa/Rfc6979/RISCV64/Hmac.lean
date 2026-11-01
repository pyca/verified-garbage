module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.Common
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Sha256.Stream

/-!
# Deterministic ECDSA on RISC-V: one HMAC

`HMAC_K(parts)` (`Cfg.hmac`), for the key `K` at the frame's `K` and a
message in parts, each in the frame after the save area or the private key
`d` (`PartOk`), written to the frame at `dst`: HMAC's `init` with `K`
(`initArgs_ok`, `init_ok`), the streaming `update` on the inner state with
each part (`updArgs_ok`, `updc_ok`, `upds_ok`), and HMAC's `finalize`
(`finArgs_ok`, `fin_ok`). Until `finalize`, memory changes only in the
states (in `scratch`) and the stack below the frame (`St`), so the key and
the parts are those at the start; `hmac_ok` composes the pieces, which the
proof of constant time relates one by one.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.RISCV64

open VG.RISCV64
open VG.RISCV64.Steps (Upd Mupd wp_mv wp_addi wp_li)
open VG.Impl.Ecdsa.Rfc6979.RISCV64
open VG.Impl.Hmac.Stream.RISCV64 (Hash mov)
open VG.Proof.Hmac.Stream.RISCV64 (HashOK)
open VG.Proof.Hmac.Common (bytesAt_length xorPad_length)
open Spec.Hmac (xorPad ipad opad blockKey hmacBlockKey)
open Spec.Sha256 (bytesAt)

/-- Reads registers through register writes (`Upd`), deciding which register
each writes. -/
macro "upd_simp" " [" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  (set_option linter.unusedSimpArgs false in simp (disch := decide) only [$ls,*]))

/-! ## The parts of a message -/

/-- What a part's base register holds. -/
def regV (s₀ : State) : Reg → Addr
  | .s1 => s₀.sp
  | .s3 => dk s₀
  | _ => 0

/-- Where a part is. -/
def pA (s₀ : State) (p : Part) : Addr := regV s₀ p.1 + BitVec.ofNat 64 p.2.1

/-- A part in the frame after the save area, or a prefix of `d`. -/
def PartOk (p : Part) : Prop :=
  (p.1 = .s1 ∧ 64 ≤ p.2.1 ∧ p.2.1 + p.2.2 ≤ frB) ∨ (p.1 = .s3 ∧ p.2.1 = 0 ∧ p.2.2 ≤ 32)

theorem PartOk.len {p : Part} (h : PartOk p) : p.2.2 ≤ 224 := by
  rcases h with ⟨-, -, h₂⟩ | ⟨-, -, h₂⟩
  · simp only [frB] at h₂; omega
  · omega

theorem PartOk.off {p : Part} (h : PartOk p) : p.2.1 < 2048 := by
  rcases h with ⟨-, -, h₂⟩ | ⟨-, h₂, -⟩
  · simp only [frB] at h₂; omega
  · omega

theorem PartOk.reg {p : Part} (h : PartOk p) : p.1 = .s1 ∨ p.1 = .s3 := by
  rcases h with ⟨h', -⟩ | ⟨h', -⟩ <;> simp [h']

/-- The message. -/
def msgOf (m : Mem) (s₀ : State) : List Part → List Byte
  | [] => []
  | p :: ps => bytesAt m (pA s₀ p) p.2.2 ++ msgOf m s₀ ps

theorem msgOf_length (m : Mem) (s₀ : State) : ∀ ps, (msgOf m s₀ ps).length = total ps
  | [] => rfl
  | p :: ps => by simp only [msgOf, List.length_append, bytesAt_length, msgOf_length m s₀ ps, total]

/-- The states' region in `scratch`. -/
abbrev stR (s₀ : State) : Region := cR s₀ 0 384

/-- The key's bytes. -/
abbrev kOf (P : Rfc) (s₀ : State) (m : Mem) : List Byte := bytesAt m (sA s₀ fK) P.c.H.D

/-- The key's block, for HMAC's pads. -/
abbrev k0Of (P : Rfc) (s₀ : State) (m : Mem) : List Byte := blockKey P.hH.SH.H (kOf P s₀ m)

theorem blockKey_length (P : Rfc) (k : List Byte) : (blockKey P.hH.SH.H k).length = P.c.H.B := by
  have hB := P.hH.hB
  have hDB : P.c.H.D ≤ P.c.H.B := by have := (sizes P).D; rcases P.hH.hB64 with h | h <;> omega
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

theorem d_apart {n : Nat} (h : n ≤ 32) : ∀ r ∈ [stR s₀, stk P s₀], Region.Disjoint ⟨dk s₀, n⟩ r := by
  have sub : Region.Sub ⟨dk s₀, n⟩ (dR s₀) := Region.sub_prefix h
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact (hp.d_c.sub_left sub).sub_right (scr_sub (by omega))
  · exact (hp.b_d.symm.sub_left sub)

theorem PartOk.apart {p : Part} (h : PartOk p) :
    ∀ r ∈ [stR s₀, stk P s₀], Region.Disjoint ⟨pA s₀ p, p.2.2⟩ r := by
  obtain ⟨r, o, n⟩ := p
  rcases h with ⟨rfl, h₁, h₂⟩ | ⟨rfl, rfl, h₂⟩
  · exact fr_apart hp (o := o) (n := n) h₂
  · simp only [pA, regV, BitVec.add_zero]
    exact d_apart hp h₂

omit hp in
/-- The bytes of a region apart from the states and the stack below the
frame are those at the start. -/
theorem St.bytes {s t : State} (h : St P s₀ s t) {a : Addr} {n : Nat}
    (hd : ∀ r ∈ [stR s₀, stk P s₀], Region.Disjoint ⟨a, n⟩ r) (hn : n ≤ 2 ^ 64) :
    bytesAt t.mem a n = bytesAt s.mem a n :=
  Proof.Sha256.Stream.bytesAt_congr fun _ hi => h.fr.bytes (R := ⟨a, n⟩) hd hn hi

theorem St.key {s t : State} (h : St P s₀ s t) : kOf P s₀ t.mem = kOf P s₀ s.mem :=
  h.bytes (fr_apart hp (by have := (sizes P).D; simp only [fK, frB]; omega)) (by have := (sizes P).D; omega)

theorem St.part {s t : State} (h : St P s₀ s t) {p : Part} (hp' : PartOk p) :
    bytesAt t.mem (pA s₀ p) p.2.2 = bytesAt s.mem (pA s₀ p) p.2.2 :=
  h.bytes (hp'.apart hp) (by have := hp'.len; omega)

theorem St.msg {s t : State} (h : St P s₀ s t) : ∀ {ps : List Part}, (∀ p ∈ ps, PartOk p) →
    msgOf t.mem s₀ ps = msgOf s.mem s₀ ps
  | [], _ => rfl
  | p :: ps, hps => by
    simp only [msgOf]
    rw [h.part hp (hps p (by simp)), h.msg (fun q hq => hps q (by simp [hq]))]

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

theorem cov_part {s : State} (hk : KR P s₀ s) {p : Part} (h : PartOk p) :
    ∃ r' ∈ s.rd ++ s.wr, ∃ off, pA s₀ p = r'.base + BitVec.ofNat 64 off ∧ off + p.2.2 ≤ r'.len := by
  obtain ⟨r, o, n⟩ := p
  rcases h with ⟨rfl, -, h₂⟩ | ⟨rfl, rfl, h₂⟩
  · exact cov_fr hp hk h₂
  · exact ⟨dR s₀, List.mem_append_left _ (by rw [hk.rd, hp.rd]; simp), 0, rfl, by simpa using h₂⟩

/-- The states, apart from each other. -/
theorem in_out : Region.Disjoint (cR s₀ sIn P.c.H.S) (cR s₀ sOut P.c.H.S) :=
  scr_disj hp (.inl (by have := (sizes P).S192; simp only [sIn, sOut]; omega)) (by have := (sizes P).S192; simp only [sIn]; omega)
    (by have := (sizes P).S192; simp only [sOut]; omega)

omit hp in
theorem st_in : Region.Sub (cR s₀ sIn P.c.H.S) (stR s₀) :=
  Offset.sub _ (by simp only [sIn]; omega) (by have := (sizes P).S192; simp only [sIn]; omega)

omit hp in
theorem st_out : Region.Sub (cR s₀ sOut P.c.H.S) (stR s₀) :=
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

theorem below_part {s : State} (hk : KR P s₀ s) {n : Nat} (hn : n ≤ P.X) {p : Part} (h : PartOk p) :
    (below s.sp n).Disjoint ⟨pA s₀ p, p.2.2⟩ := by
  obtain ⟨r, o, m⟩ := p
  rcases h with ⟨rfl, -, h₂⟩ | ⟨rfl, rfl, h₂⟩
  · exact below_fr hp hk hn h₂
  · rw [hk.sp]
    simp only [pA, regV, BitVec.add_zero]
    exact (hp.b_d.sub_left (below_stk hp hn)).sub_right (Region.sub_prefix h₂)

theorem part_st {p : Part} (h : PartOk p) {r : Region} (hr : Region.Sub r (stR s₀)) :
    Region.Disjoint ⟨pA s₀ p, p.2.2⟩ r := by
  obtain ⟨q, o, m⟩ := p
  rcases h with ⟨rfl, -, h₂⟩ | ⟨rfl, rfl, h₂⟩
  · exact fr_st hp h₂ hr
  · simp only [pA, regV, BitVec.add_zero]
    exact (hp.d_c.sub_left (Region.sub_prefix h₂)).sub_right fun x hx => scr_sub (by omega) x (hr x hx)

end

/-! ## HMAC's `init` -/

/-- After `init`'s arguments. -/
def HI (P : Rfc) (s₀ s t : State) : Prop :=
  St P s₀ s t ∧ t.gpr .a0 = cA s₀ sIn ∧ t.gpr .a1 = cA s₀ sOut ∧ t.gpr .a2 = sA s₀ fK ∧
    t.gpr .a3 = BitVec.ofNat 64 P.c.H.D

/-- After `init`: the states of the key. -/
def HK (P : Rfc) (s₀ s t : State) : Prop :=
  St P s₀ s t ∧ P.hH.SH.Repr t.mem (cA s₀ sIn) (xorPad (k0Of P s₀ s.mem) ipad) ∧
    P.hH.SH.Repr t.mem (cA s₀ sOut) (xorPad (k0Of P s₀ s.mem) opad)

section
variable {P : Rfc} {s₀ : State} (hp : Pre P s₀)
include hp

omit hp in
theorem initArgs_ok {s : State} (h : KR P s₀ s) : WP isa (.block P.c.initArgs) s (HI P s₀ s) := by
  unfold Cfg.initArgs
  have hD := (sizes P).D
  refine wp_addi (by simp only [sIn]; omega) fun s₁ u₁ => wp_addi (by simp only [sOut]; omega) fun s₂ u₂ =>
    wp_addi (by simp only [fK]; omega) fun s₃ u₃ => wp_li (by omega) fun s₄ u₄ => WP.block_nil ?_
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

theorem hi_args {s t : State} (h : HI P s₀ s t) : HiArgs P t (cA s₀ sIn) (cA s₀ sOut) (sA s₀ fK) P.c.H.D := by
  obtain ⟨St, h0, h1, h2, h3⟩ := h
  have hz := sizes P
  have hX := hz.X
  have hk : fK + P.c.H.D ≤ frB := by have := hz.D; simp only [fK, frB]; omega
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

theorem init_ok {s t : State} (h : HI P s₀ s t) : WP isa (.call P.c.hiN P.c.H.init) t (HK P s₀ s) := by
  have hz := sizes P
  have hX := hz.X
  refine hi_call (hi_args hp h) fun t' a hI hO => ?_
  have St' : St P s₀ s t' := h.1.call hp a.rd a.wr a.sp a.cs a.frame fun r hr => by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl ((st_in (P := P)))
    · exact .inl ((st_out (P := P)))
    · exact .inr ⟨_, by rw [h.1.kr.sp], hX.1⟩
  have hk : bytesAt t.mem (sA s₀ fK) P.c.H.D = kOf P s₀ s.mem := h.1.key hp
  rw [hk] at hI hO
  exact ⟨St', hI, hO⟩

end

/-! ## The streaming `update` -/

/-- After the parts `pre` were absorbed. -/
def HU (P : Rfc) (s₀ s : State) (pre : List Byte) (t : State) : Prop :=
  St P s₀ s t ∧ P.hH.SH.Repr t.mem (cA s₀ sIn) (xorPad (k0Of P s₀ s.mem) ipad ++ pre) ∧
    P.hH.SH.Repr t.mem (cA s₀ sOut) (xorPad (k0Of P s₀ s.mem) opad)

/-- After `update`'s arguments for the part `p`. -/
def HUA (P : Rfc) (s₀ s : State) (pre : List Byte) (p : Part) (t : State) : Prop :=
  HU P s₀ s pre t ∧ t.gpr .a0 = cA s₀ sIn ∧ t.gpr .a1 = BitVec.ofNat 64 (P.c.H.B + pre.length) ∧
    t.gpr .a2 = pA s₀ p ∧ t.gpr .a3 = BitVec.ofNat 64 p.2.2

section
variable {P : Rfc} {s₀ : State} (hp : Pre P s₀)
include hp

omit hp in
theorem HK.hu {s t : State} (h : HK P s₀ s t) : HU P s₀ s [] t := by
  obtain ⟨a, b, c⟩ := h
  exact ⟨a, by rw [List.append_nil]; exact b, c⟩

omit hp in
theorem updArgs_ok {s t : State} {pre : List Byte} {p : Part} (h : HU P s₀ s pre t)
    (hr : p.1 = .s1 ∨ p.1 = .s3) (hb : P.c.H.B + pre.length < 2048) (ho : p.2.1 < 2048) (hl : p.2.2 < 2048) :
    WP isa (.block (P.c.updArgs pre.length p)) t (HUA P s₀ s pre p) := by
  obtain ⟨q, o, n⟩ := p
  simp only at hr ho hl
  have hq : t.gpr q = regV s₀ q := by rcases hr with rfl | rfl; exacts [h.1.kr.s1, h.1.kr.s3]
  have q0 : q ≠ .a0 := by rcases hr with rfl | rfl <;> decide
  have q1 : q ≠ .a1 := by rcases hr with rfl | rfl <;> decide
  unfold Cfg.updArgs
  refine wp_addi (by simp only [sIn]; omega) fun s₁ u₁ => wp_li hb fun s₂ u₂ =>
    wp_addi ho fun s₃ u₃ => wp_li hl fun s₄ u₄ => WP.block_nil ?_
  have St₄ := ((((h.1).upd (by decide) u₁).upd (by decide) u₂).upd (by decide) u₃).upd (by decide) u₄
  have mm : s₄.mem = t.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine ⟨⟨St₄, by rw [mm]; exact h.2.1, by rw [mm]; exact h.2.2⟩, ?_, ?_, ?_, ?_⟩
  · upd_simp [u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
    rw [h.1.kr.s0]
  · upd_simp [u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
  · rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ q1, u₁.other _ q0, hq]; rfl
  · exact u₄.gpr

theorem updc_ok {s t : State} {pre : List Byte} {p : Part} (h : HUA P s₀ s pre p t) (hpo : PartOk p) :
    WP isa P.c.H.callUpd t (HU P s₀ s (pre ++ bytesAt s.mem (pA s₀ p) p.2.2)) := by
  obtain ⟨⟨hS, hi, ho⟩, h0, h1, h2, h3⟩ := h
  have hz := sizes P
  have hX := hz.X
  have ha : UpdArgs P t (cA s₀ sIn) (pA s₀ p) p.2.2 := by
    refine ⟨h0, h2, by rw [h3, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hpo.len; omega)], part_st hp hpo ((st_in (P := P))), by rw [hS.kr.sp]; exact hp.al,
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
  refine upd_call ha fun t' a hu => ?_
  have St' : St P s₀ s t' := hS.call hp a.rd a.wr a.sp a.cs a.frame fun r hr => by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inl ((st_in (P := P)))
    · exact .inr ⟨_, by rw [hS.kr.sp], hX.2.2.1⟩
  have hK := blockKey_length P (kOf P s₀ s.mem)
  have e := hu _ hi (by rw [h1, List.length_append, xorPad_length, hK])
  rw [List.append_assoc, hS.part hp hpo] at e
  refine ⟨St', e, P.hH.congr t.mem t'.mem _ _ (fun i hi' => ?_) ho⟩
  refine a.frame.bytes (R := cR s₀ sOut P.c.H.S) (fun r hr => ?_) (by show P.c.H.S ≤ 2 ^ 64; have := hz.S192; omega) hi'
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact (in_out hp).symm
  · exact (below_st hp hS.kr hX.2.2.1 ((st_out (P := P)))).symm

/-- The parts absorbed, one `update` each. -/
theorem upds_ok {s : State} : ∀ (ps : List Part) {t : State} {pre : List Byte}, HU P s₀ s pre t →
    (∀ p ∈ ps, PartOk p) → P.c.H.B + pre.length + total ps < 2048 →
    WP isa (P.c.upds pre.length ps) t (HU P s₀ s (pre ++ msgOf s.mem s₀ ps))
  | [], t, pre, h, _, _ => WP.block_nil (by rw [msgOf, List.append_nil]; exact h)
  | p :: ps, t, pre, h, hps, hb => by
    have hpo : PartOk p := hps p (by simp)
    have hl : p.2.2 ≤ total (p :: ps) := by simp only [total]; omega
    unfold Cfg.upds
    refine WP.seq (WP.mono (WP.seq (WP.mono (updArgs_ok h hpo.reg (by omega) hpo.off (by omega)) fun t₁ h₁ =>
      updc_ok hp h₁ hpo)) fun t₂ h₂ => ?_)
    have e : pre.length + p.2.2 = (pre ++ bytesAt s.mem (pA s₀ p) p.2.2).length := by
      rw [List.length_append, bytesAt_length]
    rw [e]
    refine WP.mono (upds_ok ps h₂ (fun q hq => hps q (by simp [hq])) (by
      rw [List.length_append, bytesAt_length]; simp only [total] at hb; omega)) fun t₃ h₃ => ?_
    rwa [List.append_assoc, ← msgOf.eq_2] at h₃

end

/-! ## HMAC's `finalize` -/

/-- After `finalize`'s arguments, for the message `msg` and the MAC to `dst`. -/
def HFA (P : Rfc) (s₀ s : State) (msg : List Byte) (dst : Nat) (t : State) : Prop :=
  HU P s₀ s msg t ∧ t.gpr .a0 = cA s₀ sIn ∧ t.gpr .a1 = cA s₀ sOut ∧
    t.gpr .a2 = BitVec.ofNat 64 (P.c.H.B + msg.length) ∧ t.gpr .a3 = sA s₀ dst

/-- After an HMAC: the MAC at `dst`, and memory changed only in the states,
the MAC and the stack below the frame. -/
def HD (P : Rfc) (s₀ s : State) (msg : List Byte) (dst : Nat) (t : State) : Prop :=
  KR P s₀ t ∧ bytesAt t.mem (sA s₀ dst) P.c.H.D = Spec.Hmac.hmac P.hH.SH.H (kOf P s₀ s.mem) msg ∧
    Frame [stR s₀, sR s₀ dst P.c.H.D, stk P s₀] s.mem t.mem ∧ ∀ r ∈ preserved, t.gpr r = s.gpr r

section
variable {P : Rfc} {s₀ : State} (hp : Pre P s₀)
include hp

omit hp in
theorem finArgs_ok {s t : State} {msg : List Byte} (h : HU P s₀ s msg t) (dst : Nat) (hb : P.c.H.B + msg.length < 2048)
    (hd : dst < 2048) : WP isa (.block (P.c.finArgs msg.length dst)) t (HFA P s₀ s msg dst) := by
  unfold Cfg.finArgs
  refine wp_addi (by simp only [sIn]; omega) fun s₁ u₁ => wp_addi (by simp only [sOut]; omega) fun s₂ u₂ =>
    wp_li hb fun s₃ u₃ => wp_addi hd fun s₄ u₄ => WP.block_nil ?_
  have St₄ := ((((h.1).upd (by decide) u₁).upd (by decide) u₂).upd (by decide) u₃).upd (by decide) u₄
  have mm : s₄.mem = t.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine ⟨⟨St₄, by rw [mm]; exact h.2.1, by rw [mm]; exact h.2.2⟩, ?_, ?_, ?_, ?_⟩
  · upd_simp [u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
    rw [h.1.kr.s0]
  · upd_simp [u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
    rw [h.1.kr.s0]
  · upd_simp [u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
  · upd_simp [u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
    rw [h.1.kr.s1]

theorem hf_args {s t : State} {msg : List Byte} {dst : Nat} (hdst : 64 ≤ dst ∧ dst + P.c.H.D ≤ frB)
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

theorem fin_ok {s t : State} {msg : List Byte} {dst : Nat} (hdst : 64 ≤ dst ∧ dst + P.c.H.D ≤ frB)
    (hm : P.c.H.B + msg.length < 2048) (h : HFA P s₀ s msg dst t) :
    WP isa (.call P.c.hfN P.c.H.finalize) t (HD P s₀ s msg dst) := by
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
    · exact ⟨sR s₀ dst P.c.H.D, by simp, fun x hx => hx⟩
    · exact ⟨stk P s₀, by simp, by rw [St.kr.sp]; exact below_stk hp hX.2.1⟩

/-- `HMAC_K(parts)` to `dst`. -/
theorem hmac_ok {s : State} (h : KR P s₀ s) {ps : List Part} (hps : ∀ p ∈ ps, PartOk p)
    (hb : P.c.H.B + total ps < 2048) {dst : Nat} (hdst : 64 ≤ dst ∧ dst + P.c.H.D ≤ frB) :
    WP isa (P.c.hmac ps dst) s (HD P s₀ s (msgOf s.mem s₀ ps) dst) := by
  unfold Cfg.hmac
  refine WP.seq (WP.mono (initArgs_ok h) fun t₁ h₁ => ?_)
  refine WP.seq (WP.mono (init_ok hp h₁) fun t₂ h₂ => ?_)
  refine WP.seq (WP.mono (upds_ok hp ps (pre := []) h₂.hu hps (by simpa using hb)) fun t₃ h₃ => ?_)
  rw [List.nil_append] at h₃
  have hl := msgOf_length s.mem s₀ ps
  refine WP.seq (WP.mono (by rw [← hl]; exact finArgs_ok h₃ dst (by omega) (by simp only [frB] at hdst; omega))
    fun t₄ h₄ => ?_)
  exact fin_ok hp hdst (by omega) h₄

end

end VG.Proof.Ecdsa.Rfc6979.RISCV64
