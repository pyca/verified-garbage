module

-- separate module: its proofs cost more than its imports, and its importers' changes need not
-- re-check them

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.Common
import VerifiedGarbage.Proof.Framework.RISCV64.Syms
import VerifiedGarbage.Proof.Framework.ICall
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Hmac.Generic.Common
import VerifiedGarbage.Proof.Pbkdf2.MdKeys
import VerifiedGarbage.Proof.Sha256.Stream

/-!
# Deterministic ECDSA on RISC-V: one HMAC, through the table

`HMAC_K(parts)` (`Cfg.hmac`), for the key `K` at the frame's `K` and a
message in parts, each in the frame after the save area or the private key
`d` (`PartOk`), written to the frame at `dst`, from the table's streaming
functions, each called indirectly (`tcall_ok`: the table's word, which `Pre`
says holds the function of the hash function, whose call an indirect call
of `f`'s functions reaches): the states for the key (`hinit_ok`: each set by
`init`, `initCall_ok`, and updated with the padded key, `padBlk_ok` and
`updCall_ok`), the inner state updated with each part (`upds_ok`), and the
MAC (`hfin_ok`: the inner state finalized, `finCall_ok`, and the outer one
updated with its digest and finalized to `dst`). Until the last
`finalize`, memory changes only in HMAC's working space in `scratch` (its
states, the padded key and the inner digest) and the stack below the frame
(`St`), so the key and the parts are those at the start; `hmac_ok`
composes the pieces.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.RISCV64

open VG.RISCV64
open VG.RISCV64.Steps (Upd Mupd wp_mv wp_addi wp_li wp_ld wp_lwu wp_sw wp_xor wp_or wp_sll)
open VG.Impl.Ecdsa.Rfc6979.RISCV64
open VG.Impl.Hmac.Stream.RISCV64 (Hash mov)
open VG.Proof.Hmac.Stream.RISCV64 (HashOK)
open VG.Proof.Hmac.Common (bytesAt_length xorPad_length)
open VG.WriteBytes (writeBytes writeBytes_append writeBytes_nil writeBytes_frame)
open Spec.Hmac (xorPad ipad opad blockKey hmacBlockKey)
open Spec.Sha256 (bytesAt)

/-- Reads registers through register writes (`Upd`), deciding which register
each writes. -/
macro "upd_simp" " [" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  (set_option linter.unusedSimpArgs false in simp (disch := decide) only [$ls,*]))

/-! ## The parts of a message -/

/-- What a base register holds. -/
def regV (s₀ : State) : Reg → Addr
  | .s0 => scr s₀
  | .s1 => s₀.sp
  | .s3 => dk s₀
  | _ => 0

/-- Where a part is. -/
def pA (s₀ : State) (p : Part) : Addr := regV s₀ p.1 + BitVec.ofNat 64 p.2.1

/-- A part in the frame after the save area, or a prefix of `d`. -/
def PartOk (P : Rfc) (p : Part) : Prop :=
  (p.1 = .s1 ∧ 64 ≤ p.2.1 ∧ p.2.1 + p.2.2 ≤ P.c.frB) ∨ (p.1 = .s3 ∧ p.2.1 = 0 ∧ p.2.2 ≤ P.Q)

theorem PartOk.len {P : Rfc} {p : Part} (h : PartOk P p) : p.2.2 ≤ 320 := by
  have := (sizes P).Q
  have := (sizes P).H
  rcases h with ⟨-, h₁, h₂⟩ | ⟨-, -, h₂⟩ <;> omega

theorem PartOk.off {P : Rfc} {p : Part} (h : PartOk P p) : p.2.1 < 2048 := by
  rcases h with ⟨-, -, h₂⟩ | ⟨-, h₂, -⟩
  · have := (sizes P).Q; have := (sizes P).H; omega
  · omega

theorem PartOk.reg {P : Rfc} {p : Part} (h : PartOk P p) : p.1 = .s1 ∨ p.1 = .s3 := by
  rcases h with ⟨h', -⟩ | ⟨h', -⟩ <;> simp [h']

/-- The message. -/
def msgOf (m : Mem) (s₀ : State) : List Part → List Byte
  | [] => []
  | p :: ps => bytesAt m (pA s₀ p) p.2.2 ++ msgOf m s₀ ps

theorem msgOf_length (m : Mem) (s₀ : State) : ∀ ps, (msgOf m s₀ ps).length = total ps
  | [] => rfl
  | p :: ps => by simp only [msgOf, List.length_append, bytesAt_length, msgOf_length m s₀ ps, total]

/-- HMAC's working space in `scratch`: its states, the padded key and the
inner digest. -/
abbrev stR (s₀ : State) : Region := cR s₀ 0 576

/-- The key's bytes. -/
abbrev kOf (P : Rfc) (s₀ : State) (m : Mem) : List Byte := bytesAt m (sA s₀ fK) P.c.D

/-- The key's block, for HMAC's pads. -/
abbrev k0Of (P : Rfc) (s₀ : State) (m : Mem) : List Byte := blockKey P.hH.SH.H (kOf P s₀ m)

theorem blockKey_length (P : Rfc) (k : List Byte) : (blockKey P.hH.SH.H k).length = P.c.B := by
  have hB := P.hH.hB
  have hz := sizes P
  have hDB : P.H.D ≤ P.H.B := by have := hz.D; have := hz.DB; rcases hz.B with h | h <;> omega
  rw [← hz.DB.2.1]
  simp only [blockKey, hB, List.length_append, List.length_replicate]
  split
  · rw [P.hH.hashLen]; omega
  · omega

/-! ## What holds between the calls -/

/-- From the start `s` of an HMAC: `KR`, and memory changed only in HMAC's
working space and the stack below the frame. -/
structure St (P : Rfc) (s₀ s t : State) : Prop where
  kr : KR P s₀ t
  fr : Frame [stR s₀, stk P s₀] s.mem t.mem
  pr : ∀ r ∈ preserved, t.gpr r = s.gpr r

section
variable {P : Rfc} {s₀ : State} (hp : Pre P s₀)
include hp

/-- Regions of the frame are apart from what the calls of an HMAC write. -/
theorem fr_apart {o n : Nat} (h : o + n ≤ P.c.frB) : ∀ r ∈ [stR s₀, stk P s₀], Region.Disjoint (sR s₀ o n) r := by
  have sub : Region.Sub (sR s₀ o n) (frR P s₀) := part_sub h
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
    ∀ r ∈ [stR s₀, stk P s₀], Region.Disjoint ⟨pA s₀ p, p.2.2⟩ r := by
  obtain ⟨r, o, n⟩ := p
  rcases h with ⟨rfl, h₁, h₂⟩ | ⟨rfl, rfl, h₂⟩
  · exact fr_apart hp (o := o) (n := n) h₂
  · simp only [pA, regV, BitVec.add_zero]
    exact d_apart hp h₂

omit hp in
/-- The bytes of a region apart from HMAC's working space and the stack below
the frame are those at the start. -/
theorem St.bytes {s t : State} (h : St P s₀ s t) {a : Addr} {n : Nat}
    (hd : ∀ r ∈ [stR s₀, stk P s₀], Region.Disjoint ⟨a, n⟩ r) (hn : n ≤ 2 ^ 64) :
    bytesAt t.mem a n = bytesAt s.mem a n :=
  Proof.Sha256.Stream.bytesAt_congr fun _ hi => h.fr.bytes (R := ⟨a, n⟩) hd hn hi

theorem St.key {s t : State} (h : St P s₀ s t) : kOf P s₀ t.mem = kOf P s₀ s.mem :=
  h.bytes (fr_apart hp (by have := (sizes P).D; simp only [fK]; have := (sizes P).Q; have := (sizes P).H; omega))
    (by have := (sizes P).D; omega)

theorem St.part {s t : State} (h : St P s₀ s t) {p : Part} (hp' : PartOk P p) :
    bytesAt t.mem (pA s₀ p) p.2.2 = bytesAt s.mem (pA s₀ p) p.2.2 :=
  h.bytes (hp'.apart hp) (by have := hp'.len; omega)

theorem St.msg {s t : State} (h : St P s₀ s t) : ∀ {ps : List Part}, (∀ p ∈ ps, PartOk P p) →
    msgOf t.mem s₀ ps = msgOf s.mem s₀ ps
  | [], _ => rfl
  | p :: ps, hps => by
    simp only [msgOf]
    rw [h.part hp (hps p (by simp)), h.msg (fun q hq => hps q (by simp [hq]))]

omit hp in
theorem St.refl {s : State} (h : KR P s₀ s) : St P s₀ s s := ⟨h, Frame.refl _ _, fun _ _ => rfl⟩

/-- A call that writes HMAC's working space and the stack below the frame keeps `St`. -/
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

theorem cov_fr {s : State} (hk : KR P s₀ s) {o n : Nat} (h : o + n ≤ P.c.frB) :
    ∃ r' ∈ s.rd ++ s.wr, ∃ off, (sR s₀ o n).base = r'.base + BitVec.ofNat 64 off ∧ off + (sR s₀ o n).len ≤ r'.len :=
  ⟨frR P s₀, List.mem_append_right _ (fr_wr hp hk.wr), o, rfl, h⟩

theorem covW_fr {s : State} (hk : KR P s₀ s) {o n : Nat} (h : o + n ≤ P.c.frB) :
    ∃ r' ∈ s.wr, ∃ off, (sR s₀ o n).base = r'.base + BitVec.ofNat 64 off ∧ off + (sR s₀ o n).len ≤ r'.len :=
  ⟨frR P s₀, fr_wr hp hk.wr, o, rfl, h⟩

theorem cov_scr {s : State} (hk : KR P s₀ s) {o n : Nat} (h : o + n ≤ 8192) :
    ∃ r' ∈ s.rd ++ s.wr, ∃ off, (cR s₀ o n).base = r'.base + BitVec.ofNat 64 off ∧ off + (cR s₀ o n).len ≤ r'.len :=
  ⟨scrR s₀, List.mem_append_right _ (scr_wr hp hk.wr), o, rfl, h⟩

theorem covW_scr {s : State} (hk : KR P s₀ s) {o n : Nat} (h : o + n ≤ 8192) :
    ∃ r' ∈ s.wr, ∃ off, (cR s₀ o n).base = r'.base + BitVec.ofNat 64 off ∧ off + (cR s₀ o n).len ≤ r'.len :=
  ⟨scrR s₀, scr_wr hp hk.wr, o, rfl, h⟩

theorem cov_part {s : State} (hk : KR P s₀ s) {p : Part} (h : PartOk P p) :
    ∃ r' ∈ s.rd ++ s.wr, ∃ off, pA s₀ p = r'.base + BitVec.ofNat 64 off ∧ off + p.2.2 ≤ r'.len := by
  obtain ⟨r, o, n⟩ := p
  rcases h with ⟨rfl, -, h₂⟩ | ⟨rfl, rfl, h₂⟩
  · exact cov_fr hp hk h₂
  · exact ⟨dR P s₀, List.mem_append_left _ (by rw [hk.rd, hp.rd]; simp), 0, rfl, by simpa using h₂⟩

/-- The states, apart from each other. -/
theorem in_out : Region.Disjoint (cR s₀ sIn P.H.S) (cR s₀ sOut P.H.S) :=
  scr_disj hp (.inl (by have := (sizes P).S192; simp only [sIn, sOut]; omega)) (by have := (sizes P).S192; simp only [sIn]; omega)
    (by have := (sizes P).S192; simp only [sOut]; omega)

omit hp in
theorem st_sub {o n : Nat} (h : o + n ≤ 576) : Region.Sub (cR s₀ o n) (stR s₀) :=
  Offset.sub _ (by omega) h

/-- A part of the frame is apart from HMAC's working space. -/
theorem fr_st {o n : Nat} (h : o + n ≤ P.c.frB) {r : Region} (hr : Region.Sub r (stR s₀)) :
    Region.Disjoint (sR s₀ o n) r :=
  (hp.f_c.sub_left (part_sub h)).sub_right fun x hx => scr_sub (by omega) x (hr x hx)

/-- The stack below the stack pointer is apart from HMAC's working space and the frame. -/
theorem below_st {s : State} (hk : KR P s₀ s) {n : Nat} (hn : n ≤ P.X) {r : Region} (hr : Region.Sub r (stR s₀)) :
    (below s.sp n).Disjoint r := by
  rw [hk.sp]
  exact (hp.b_c.sub_left (below_stk hp hn)).sub_right fun x hx => scr_sub (by omega) x (hr x hx)

theorem below_fr {s : State} (hk : KR P s₀ s) {n : Nat} (hn : n ≤ P.X) {o m : Nat} (h : o + m ≤ P.c.frB) :
    (below s.sp n).Disjoint (sR s₀ o m) := by
  rw [hk.sp]
  exact ((f_s hp).sub_left (part_sub h)).symm.sub_left (below_stk hp hn)

theorem below_part {s : State} (hk : KR P s₀ s) {n : Nat} (hn : n ≤ P.X) {p : Part} (h : PartOk P p) :
    (below s.sp n).Disjoint ⟨pA s₀ p, p.2.2⟩ := by
  obtain ⟨r, o, m⟩ := p
  rcases h with ⟨rfl, -, h₂⟩ | ⟨rfl, rfl, h₂⟩
  · exact below_fr hp hk hn h₂
  · rw [hk.sp]
    simp only [pA, regV, BitVec.add_zero]
    exact (hp.b_d.sub_left (below_stk hp hn)).sub_right (Region.sub_prefix h₂)

theorem part_st {p : Part} (h : PartOk P p) {r : Region} (hr : Region.Sub r (stR s₀)) :
    Region.Disjoint ⟨pA s₀ p, p.2.2⟩ r := by
  obtain ⟨q, o, m⟩ := p
  rcases h with ⟨rfl, -, h₂⟩ | ⟨rfl, rfl, h₂⟩
  · exact fr_st hp h₂ hr
  · simp only [pA, regV, BitVec.add_zero]
    exact (hp.d_c.sub_left (Region.sub_prefix h₂)).sub_right fun x hx => scr_sub (by omega) x (hr x hx)

end

/-! ## The data of an `update` -/

/-- Data `update` may read: a part, or HMAC's padded key or inner digest
(`len` bytes at `off` from `scratch`, after the states). -/
def DatOk (P : Rfc) (base : Reg) (off len : Nat) : Prop :=
  PartOk P (base, off, len) ∨ (base = .s0 ∧ 384 ≤ off ∧ off + len ≤ 576)

section
variable {P : Rfc} {s₀ : State} (hp : Pre P s₀)
include hp

theorem DatOk.cov {s : State} (hk : KR P s₀ s) {base : Reg} {off len : Nat} (h : DatOk P base off len) :
    ∃ r' ∈ s.rd ++ s.wr, ∃ o, pA s₀ (base, off, len) = r'.base + BitVec.ofNat 64 o ∧ o + len ≤ r'.len := by
  rcases h with h | ⟨rfl, _, h₂⟩
  · exact cov_part hp hk h
  · exact cov_scr hp hk (o := off) (n := len) (by omega)

theorem DatOk.below {s : State} (hk : KR P s₀ s) {n : Nat} (hn : n ≤ P.X) {base : Reg} {off len : Nat}
    (h : DatOk P base off len) : (below s.sp n).Disjoint ⟨pA s₀ (base, off, len), len⟩ := by
  rcases h with h | ⟨rfl, h₁, h₂⟩
  · exact below_part hp hk hn h
  · exact below_st hp hk hn (st_sub (o := off) (n := len) h₂)

/-- The data is apart from the states. -/
theorem DatOk.st {base : Reg} {off len : Nat} (h : DatOk P base off len) {o : Nat} (ho : o + P.H.S ≤ 384) :
    Region.Disjoint ⟨pA s₀ (base, off, len), len⟩ (cR s₀ o P.H.S) := by
  rcases h with h | ⟨rfl, h₁, h₂⟩
  · exact part_st hp h (st_sub (by omega))
  · exact scr_disj hp (a := off) (m := len) (.inr (by omega)) (by omega) (by omega)

omit hp in
theorem DatOk.off {base : Reg} {off len : Nat} (h : DatOk P base off len) : off < 2048 ∧ len ≤ 320 := by
  rcases h with h | ⟨-, h₁, h₂⟩
  · exact ⟨h.off, h.len⟩
  · omega

omit hp in
theorem DatOk.reg {s : State} (hk : KR P s₀ s) {base : Reg} {off len : Nat} (h : DatOk P base off len) :
    s.gpr base = regV s₀ base := by
  rcases h with h | ⟨rfl, -⟩
  · rcases h.reg with h' | h'
    · simp only at h'; subst h'; exact hk.s1
    · simp only at h'; subst h'; exact hk.s3
  · exact hk.s0

end

/-! ## The table's calls -/

section
variable {P : Rfc} {s₀ : State} (hp : Pre P s₀)
include hp

/-- The table's word `k` is as on entry. -/
theorem tabWord {t : State} (hk : KR P s₀ t) {k : Nat} (hk5 : k < 5) :
    t.mem.readW (tab s₀ + BitVec.ofNat 64 (8 * k)) 64 = s₀.mem.readW (tab s₀ + BitVec.ofNat 64 (8 * k)) 64 := by
  have hc : (tabR s₀).Contains (tab s₀ + BitVec.ofNat 64 (8 * k)) 8 :=
    Offset.contains_base _ (by omega) (by have := hp.bn; omega)
  refine Mem.readW_congr fun b hb => hk.frame _ fun r hr hc' => hp.b_w r hr _ ?_ hc'
  simp only [Region.Contains] at hc ⊢
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Mem.sub_ofNat_toNat _ (by have := hp.bn; omega)]
  have := hp.bn
  omega

/-- The call of the table's function `k`, among `ts`, which reaches `n`, as
the call of `n` from the state the load of its address leaves. -/
theorem tcall_ok {t : State} (hk : KR P s₀ t) (hsy : t.syms = s₀.syms) {k : Nat} (hk3 : k < 3)
    {ts : List (String × Prog isa)} {n : String} {c : Prog isa}
    (hf : ts.find? (fun q => s₀.syms q.1 == s₀.syms n) = some (n, c))
    (hw : s₀.mem.readW (tab s₀ + BitVec.ofNat 64 (8 * k)) 64 = s₀.syms n) {Q : State → Prop}
    (kk : ∀ t', Upd t t' .t1 (s₀.syms n) → t'.syms = s₀.syms → WP isa (.call n c) t' Q) :
    WP isa (tcall k ts) t Q := by
  unfold tcall tword
  have hin : InRegions (t.rd ++ t.wr) (tab s₀ + BitVec.ofNat 64 (8 * k)) 8 :=
    ⟨tabR s₀, List.mem_append_left _ (by rw [hk.rd, hp.rd]; simp),
      Offset.contains_base _ (by omega) (by have := hp.bn; omega)⟩
  refine WP.seq (WP.of_syms (wp_ld (a := tab s₀ + BitVec.ofNat 64 (8 * k)) (by omega)
    (by rw [hk.s6]) (by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]
      have := hp.ba; have := hp.bn; omega) hin fun t' u => WP.block_nil fun sy' => ?_))
  rw [tabWord hp hk (by omega), hw] at u
  refine WP.icalls_of_call (a := t'.gpr .t1) rfl ?_ (kk t' u (sy'.trans hsy))
  show ts.find? (fun q => t'.syms q.1 == t'.gpr .t1) = _
  rw [u.gpr, sy', hsy]; exact hf

end

/-! ## The streaming calls -/

section
variable {P : Rfc} {s₀ : State} (hp : Pre P s₀)
include hp

omit hp in
/-- A state's representation is kept by memory that changed apart from it. -/
theorem repr_keep {m m' : Mem} {ws : List Region} (hf : Frame ws m m') {o : Nat}
    (hd : ∀ r ∈ ws, Region.Disjoint (cR s₀ o P.H.S) r) {x : List Byte} (h : P.hH.SH.Repr m (cA s₀ o) x) :
    P.hH.SH.Repr m' (cA s₀ o) x :=
  P.hH.congr m m' _ _ (fun i hi => hf.bytes (R := cR s₀ o P.H.S) hd (by show P.H.S ≤ 2 ^ 64; have := (sizes P).S192; omega) hi) h

/-- The streaming `init` of the state at `scratch + o`. -/
theorem initT_ok {s t₁ : State} (S₁ : St P s₀ s t₁) (sy₁ : t₁.syms = s₀.syms) {o : Nat} (ho : o + P.H.S ≤ 384)
    (h0 : t₁.gpr .a0 = cA s₀ o) :
    WP isa (tcall 0 P.c.f.init) t₁ fun t' => St P s₀ s t' ∧ t'.syms = s₀.syms ∧
      P.hH.SH.Repr t'.mem (cA s₀ o) [] ∧ Frame [cR s₀ o P.H.S, below s₀.sp P.X] t₁.mem t'.mem := by
  have hz := sizes P
  have hX := hz.X
  refine tcall_ok hp S₁.kr sy₁ (k := 0) (by decide) hp.bo.i
    (by rw [Nat.mul_zero, BitVec.add_zero]; exact hp.bm.1) fun t₂ u₂ sy₂ => ?_
  have S₂ := S₁.upd (by decide) u₂
  refine WP.of_syms (P.hH.callInit_ok (s := t₂) (st := cA s₀ o) (by rw [u₂.other _ (by decide), h0])
    (VG.Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact cov_scr hp S₂.kr (by omega))
    (VG.Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact covW_scr hp S₂.kr (by omega))
    fun t₃ hrd hwr hsp hf hcs hr sy₃ => ?_)
  have hsp₂ : t₂.sp = s₀.sp := S₂.kr.sp
  have hw : ∀ r ∈ [cR s₀ o P.H.S] ++ [below t₂.sp P.H.F],
      Region.Sub r (stR s₀) ∨ ∃ n, r = below s₀.sp n ∧ n ≤ P.X := fun r hr => by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inl (st_sub (by omega))
    · exact .inr ⟨_, by rw [hsp₂], hX.1⟩
  refine ⟨S₂.call hp hrd hwr hsp hcs hf hw, sy₃.trans sy₂, hr, ?_⟩
  have e : t₂.mem = t₁.mem := by rw [u₂.mem]
  rw [← e]
  refine hf.sub fun r hr => ?_
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨_, by simp, fun x hx => hx⟩
  · exact ⟨below s₀.sp P.X, by simp, by rw [hsp₂]; exact below_sub hX.1 (by have := hp.spX; have := s₀.sp.isLt; omega)⟩

/-- The streaming `init` of the state at `scratch + o`. -/
theorem initCall_ok {s t : State} (h : St P s₀ s t) (hsy : t.syms = s₀.syms) {o : Nat} (ho : o + P.H.S ≤ 384) :
    WP isa (P.c.initCall o) t fun t' => St P s₀ s t' ∧ t'.syms = s₀.syms ∧
      P.hH.SH.Repr t'.mem (cA s₀ o) [] ∧ Frame [cR s₀ o P.H.S, below s₀.sp P.X] t.mem t'.mem := by
  unfold Cfg.initCall
  refine WP.seq (WP.of_syms (wp_addi (imm := o) (by omega) fun t₁ u₁ => WP.block_nil fun sy₁ => ?_))
  have e : t₁.mem = t.mem := u₁.mem
  rw [← e]
  exact initT_ok hp (h.upd (by decide) u₁) (sy₁.trans hsy) ho (by rw [u₁.gpr, h.kr.s0])

/-- The streaming `update` of the state at `scratch + o`, which holds `cnt`
bytes, with the data `len` bytes at `off(base)`. -/
theorem updT_ok {s t₄ : State} (S₄ : St P s₀ s t₄) (sy₄ : t₄.syms = s₀.syms) {o cnt : Nat} (ho : o + P.H.S ≤ 384)
    {base : Reg} {off len : Nat} (hd : DatOk P base off len) (g0 : t₄.gpr .a0 = cA s₀ o)
    (g1 : t₄.gpr .a1 = BitVec.ofNat 64 cnt) (g2 : t₄.gpr .a2 = pA s₀ (base, off, len)) (g3 : (t₄.gpr .a3).toNat = len) :
    WP isa (tcall 1 P.c.f.upd) t₄ fun t' => St P s₀ s t' ∧ t'.syms = s₀.syms ∧
      (∀ m, P.hH.SH.Repr t₄.mem (cA s₀ o) m → cnt = m.length →
        P.hH.SH.Repr t'.mem (cA s₀ o) (m ++ bytesAt t₄.mem (pA s₀ (base, off, len)) len)) ∧
      Frame [cR s₀ o P.H.S, below s₀.sp P.X] t₄.mem t'.mem := by
  have hz := sizes P
  have hX := hz.X
  refine tcall_ok hp S₄.kr sy₄ (k := 1) (by decide) hp.bo.u hp.bm.2.1 fun t₅ u₅ sy₅ => ?_
  have S₅ := S₄.upd (by decide) u₅
  have hsp₅ : t₅.sp = s₀.sp := S₅.kr.sp
  refine WP.of_syms (P.hH.callUpd_ok (s := t₅) (st := cA s₀ o) (dat := pA s₀ (base, off, len)) (len := len)
    (by rw [u₅.other _ (by decide), g0]) (by rw [u₅.other _ (by decide), g2]) (by rw [u₅.other _ (by decide), g3])
    (hd.st hp ho) (by rw [hsp₅]; exact hp.al) (by rw [hsp₅]; have := hp.spX; omega)
    (below_st hp S₅.kr hX.1 (st_sub (by omega))) (hd.below hp S₅.kr hX.1)
    (VG.Covers.of_sub fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hd.cov hp S₅.kr
      · exact cov_scr hp S₅.kr (by omega))
    (VG.Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact covW_scr hp S₅.kr (by omega))
    fun t₆ hrd hwr hsp hf hcs hr sy₆ => ?_)
  have hw : ∀ r ∈ [cR s₀ o P.H.S] ++ [below t₅.sp P.H.F],
      Region.Sub r (stR s₀) ∨ ∃ n, r = below s₀.sp n ∧ n ≤ P.X := fun r hr => by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inl (st_sub (by omega))
    · exact .inr ⟨_, by rw [hsp₅], hX.1⟩
  have e : t₅.mem = t₄.mem := by rw [u₅.mem]
  refine ⟨S₅.call hp hrd hwr hsp hcs hf hw, sy₆.trans sy₅, fun m hm hl => ?_, ?_⟩
  · have := hr m (by rw [e]; exact hm) (by rw [u₅.other _ (by decide), g1, hl])
    rwa [e] at this
  · rw [← e]
    refine hf.sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, by simp, fun x hx => hx⟩
    · exact ⟨below s₀.sp P.X, by simp, by
        rw [hsp₅]; exact below_sub hX.1 (by have := hp.spX; have := s₀.sp.isLt; omega)⟩

/-- The streaming `update` of the state at `scratch + o`, which holds `cnt`
bytes, with the data `len` bytes at `off(base)`. -/
theorem updCall_ok {s t : State} (h : St P s₀ s t) (hsy : t.syms = s₀.syms) {o cnt : Nat} (ho : o + P.H.S ≤ 384)
    (hcnt : cnt < 2048) {base : Reg} {off len : Nat} (hd : DatOk P base off len) :
    WP isa (P.c.updCall o cnt base off len) t fun t' => St P s₀ s t' ∧ t'.syms = s₀.syms ∧
      (∀ m, P.hH.SH.Repr t.mem (cA s₀ o) m → cnt = m.length →
        P.hH.SH.Repr t'.mem (cA s₀ o) (m ++ bytesAt t.mem (pA s₀ (base, off, len)) len)) ∧
      Frame [cR s₀ o P.H.S, below s₀.sp P.X] t.mem t'.mem := by
  have hz := sizes P
  have hX := hz.X
  obtain ⟨hoff, hlen⟩ := hd.off
  have hb := hd.reg h.kr
  unfold Cfg.updCall Cfg.updArgs
  refine WP.seq (WP.of_syms (wp_addi (imm := o) (by omega) fun t₁ u₁ => wp_li (imm := cnt) hcnt fun t₂ u₂ =>
    wp_addi (imm := off) hoff fun t₃ u₃ => wp_li (imm := len) (by omega) fun t₄ u₄ => WP.block_nil fun sy₄ => ?_))
  have S₄ := (((h.upd (by decide) u₁).upd (by decide) u₂).upd (by decide) u₃).upd (by decide) u₄
  have m₄ : t₄.mem = t.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have hbne : base ≠ .a0 ∧ base ≠ .a1 := by
    rcases hd with h' | ⟨rfl, -⟩
    · rcases h'.reg with e | e <;> (simp only at e; subst e; decide)
    · decide
  rw [← m₄]
  refine updT_ok hp S₄ (sy₄.trans hsy) ho hd ?_ ?_ ?_ ?_
  · upd_simp [u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]; rw [h.kr.s0]
  · upd_simp [u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
  · rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ hbne.2, u₁.other _ hbne.1, hb]; rfl
  · rw [u₄.gpr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

/-- Where `finalize` may write its digest: the inner digest's place in
`scratch`, or the frame after the save area. -/
def OutOk (P : Rfc) (base : Reg) (off : Nat) : Prop :=
  (base = .s0 ∧ off = sTmp) ∨ (base = .s1 ∧ 64 ≤ off ∧ off + P.c.D ≤ P.c.frB)

/-- The streaming `finalize` of the state at `scratch + o`, which holds `cnt`
bytes, with its digest to `off(base)`. -/
theorem finT_ok {t₃ : State} (k₃ : KR P s₀ t₃) (sy₃ : t₃.syms = s₀.syms) {o cnt : Nat} (ho : o + P.H.S ≤ 384)
    {base : Reg} {off : Nat} (hd : OutOk P base off) (g0 : t₃.gpr .a0 = cA s₀ o)
    (g1 : t₃.gpr .a1 = BitVec.ofNat 64 cnt) (g2 : t₃.gpr .a2 = pA s₀ (base, off, P.c.D)) :
    WP isa (tcall 2 P.c.f.fin) t₃ fun t' => KR P s₀ t' ∧ t'.syms = s₀.syms ∧
      (∀ r ∈ preserved, t'.gpr r = t₃.gpr r) ∧
      (∀ m, P.hH.SH.Repr t₃.mem (cA s₀ o) m → m.length < 2 ^ 64 → cnt = m.length →
        bytesAt t'.mem (pA s₀ (base, off, P.c.D)) P.c.D = P.hH.SH.H.hash m) ∧
      Frame [cR s₀ o P.H.S, ⟨pA s₀ (base, off, P.c.D), P.c.D⟩, below s₀.sp P.X] t₃.mem t'.mem := by
  have hz := sizes P
  have hX := hz.X
  have hzH := hz.H
  have hzQ := hz.Q
  obtain ⟨hD1, hD2⟩ := hz.D
  have hDH : P.H.D = P.c.D := hz.DB.1
  -- The digest's region: in `scratch` or the frame.
  have hW : Region.Sub ⟨pA s₀ (base, off, P.c.D), P.c.D⟩ (stR s₀) ∨
      ((∃ o' n, (⟨pA s₀ (base, off, P.c.D), P.c.D⟩ : Region) = sR s₀ o' n ∧ 64 ≤ o' ∧ o' + n ≤ P.c.frB)) := by
    rcases hd with ⟨rfl, rfl⟩ | ⟨rfl, h₁, h₂⟩
    · exact .inl (st_sub (o := sTmp) (n := P.c.D) (by simp only [sTmp]; omega))
    · exact .inr ⟨off, P.c.D, rfl, h₁, h₂⟩
  have hcovO : ∀ {s : State}, KR P s₀ s →
      ∃ r' ∈ s.wr, ∃ o', pA s₀ (base, off, P.c.D) = r'.base + BitVec.ofNat 64 o' ∧ o' + P.c.D ≤ r'.len :=
    fun {s} k => by
      rcases hd with ⟨rfl, rfl⟩ | ⟨rfl, h₁, h₂⟩
      · exact covW_scr hp k (o := sTmp) (n := P.c.D) (by simp only [sTmp]; omega)
      · exact covW_fr hp k h₂
  have hdO : Region.Disjoint (cR s₀ o P.H.S) ⟨pA s₀ (base, off, P.c.D), P.c.D⟩ := by
    rcases hd with ⟨rfl, rfl⟩ | ⟨rfl, h₁, h₂⟩
    · exact scr_disj hp (.inl (by simp only [sTmp]; omega)) (by omega) (by simp only [sTmp]; omega)
    · exact (fr_st hp h₂ (st_sub (by omega))).symm
  refine tcall_ok hp k₃ sy₃ (k := 2) (by decide) hp.bo.f hp.bm.2.2 fun t₄ u₄ sy₄ => ?_
  have k₄ := k₃.upd (by decide) u₄
  have hsp₄ : t₄.sp = s₀.sp := k₄.sp
  have hbS : (below t₄.sp P.H.F).Disjoint ⟨pA s₀ (base, off, P.c.D), P.c.D⟩ := by
    rcases hW with h' | ⟨o', n, e, h₁, h₂⟩
    · exact below_st hp k₄ hX.1 h'
    · rw [e]; exact below_fr hp k₄ hX.1 h₂
  refine WP.of_syms (P.hH.callFin_ok (s := t₄) (st := cA s₀ o) (o := pA s₀ (base, off, P.c.D))
    (by rw [u₄.other _ (by decide), g0]) (by rw [u₄.other _ (by decide), g2]) (by rw [hDH]; exact hdO)
    (by rw [hsp₄]; exact hp.al) (by rw [hsp₄]; have := hp.spX; omega)
    (below_st hp k₄ hX.1 (st_sub (by omega))) (by rw [hDH]; exact hbS)
    (VG.Covers.of_sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact cov_scr hp k₄ (by omega)
      · obtain ⟨r', hr', o', h₁, h₂⟩ := hcovO k₄
        exact ⟨r', List.mem_append_right _ hr', o', by rw [h₁], by rw [hDH]; exact h₂⟩)
    (VG.Covers.of_sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact covW_scr hp k₄ (by omega)
      · obtain ⟨r', hr', o', h₁, h₂⟩ := hcovO k₄
        exact ⟨r', hr', o', by rw [h₁], by rw [hDH]; exact h₂⟩)
    fun t₅ hrd hwr hsp hf hcs hr sy₅ => ?_)
  rw [hDH] at hf hr
  have hwk : ∀ r ∈ [cR s₀ o P.H.S, ⟨pA s₀ (base, off, P.c.D), P.c.D⟩] ++ [below t₄.sp P.H.F], Wk P s₀ r :=
    fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact .inr (.inr (.inl (scr_sub (by omega))))
      · rcases hW with h' | h'
        · exact .inr (.inr (.inl fun x hx => scr_sub (by omega) x (h' x hx)))
        · exact .inl h'
      · exact .inr (.inr (.inr ⟨_, by rw [hsp₄], hX.1⟩))
  have e : t₄.mem = t₃.mem := u₄.mem
  have pr₄ : ∀ r ∈ preserved, t₄.gpr r = t₃.gpr r := fun r hr => u₄.other r (by revert r; decide)
  refine ⟨k₄.call hp hrd hwr hsp hcs hf hwk, sy₅.trans sy₄, fun r hr => (hcs r hr).trans (pr₄ r hr), fun m hm hl hc => ?_, ?_⟩
  · exact hr m (by rw [e]; exact hm) hl (by rw [u₄.other _ (by decide), g1, hc])
  · rw [← e]
    refine hf.sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, by simp, fun x hx => hx⟩
    · exact ⟨_, by simp, fun x hx => hx⟩
    · exact ⟨below s₀.sp P.X, by simp, by
        rw [hsp₄]; exact below_sub hX.1 (by have := hp.spX; have := s₀.sp.isLt; omega)⟩

/-- The streaming `finalize` of the state at `scratch + o`, which holds `cnt`
bytes, with its digest to `off(base)`. -/
theorem finCall_ok {t : State} (hk : KR P s₀ t) (hsy : t.syms = s₀.syms) {o cnt : Nat} (ho : o + P.H.S ≤ 384)
    (hcnt : cnt < 2048) {base : Reg} {off : Nat} (hd : OutOk P base off) :
    WP isa (P.c.finCall o cnt base off) t fun t' => KR P s₀ t' ∧ t'.syms = s₀.syms ∧
      (∀ r ∈ preserved, t'.gpr r = t.gpr r) ∧
      (∀ m, P.hH.SH.Repr t.mem (cA s₀ o) m → m.length < 2 ^ 64 → cnt = m.length →
        bytesAt t'.mem (pA s₀ (base, off, P.c.D)) P.c.D = P.hH.SH.H.hash m) ∧
      Frame [cR s₀ o P.H.S, ⟨pA s₀ (base, off, P.c.D), P.c.D⟩, below s₀.sp P.X] t.mem t'.mem := by
  have hz := sizes P
  have hzH := hz.H
  have hzQ := hz.Q
  have hoff : off < 2048 := by rcases hd with ⟨-, rfl⟩ | ⟨-, -, h₂⟩ <;> (try simp only [sTmp]) <;> omega
  have hb : t.gpr base = regV s₀ base := by
    rcases hd with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact hk.s0
    · exact hk.s1
  have hbne : base ≠ .a0 ∧ base ≠ .a1 := by rcases hd with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide
  unfold Cfg.finCall Cfg.finArgs
  refine WP.seq (WP.of_syms (wp_addi (imm := o) (by omega) fun t₁ u₁ => wp_li (imm := cnt) hcnt fun t₂ u₂ =>
    wp_addi (imm := off) hoff fun t₃ u₃ => WP.block_nil fun sy₃ => ?_))
  have k₃ := ((hk.upd (by decide) u₁).upd (by decide) u₂).upd (by decide) u₃
  have m₃ : t₃.mem = t.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have pr₃ : ∀ r ∈ preserved, t₃.gpr r = t.gpr r := fun r hr => by
    rw [u₃.other r (by revert r hr; decide), u₂.other r (by revert r hr; decide), u₁.other r (by revert r hr; decide)]
  rw [← m₃]
  refine WP.mono (finT_ok hp k₃ (sy₃.trans hsy) ho hd ?_ ?_ ?_) fun t' ⟨a, b, c, d, e⟩ =>
    ⟨a, b, fun r hr => (c r hr).trans (pr₃ r hr), d, e⟩
  · upd_simp [u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]; rw [hk.s0]
  · upd_simp [u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
  · rw [u₃.gpr, u₂.other _ hbne.2, u₁.other _ hbne.1, hb]; rfl

end

/-! ## The padded key -/

/-- The first `n` bytes of the key of `D` bytes at `K` (in `m`), padded with
zeros and XORed with `c` in every byte. -/
def padBytes (m : Mem) (K : Addr) (D : Nat) (c : Byte) (n : Nat) : List Byte :=
  (List.range n).map fun i => if i < D then m (K + BitVec.ofNat 64 i) ^^^ c else c

theorem padBytes_length (m : Mem) (K : Addr) (D : Nat) (c : Byte) (n : Nat) : (padBytes m K D c n).length = n := by
  simp [padBytes]

/-- Four more bytes, a word of the key's or of `c`. -/
theorem padBytes_succ (m : Mem) (K : Addr) {D : Nat} (c : Byte) {k : Nat} (hD : D % 4 = 0) :
    padBytes m K D c (4 * k + 4) = padBytes m K D c (4 * k) ++
      (if k < D / 4 then (bytesAt m (K + BitVec.ofNat 64 (4 * k)) 4).map (· ^^^ c)
       else List.replicate 4 c) := by
  simp only [padBytes, List.range_add, List.map_append, List.map_map]
  congr 1
  split
  · simp only [bytesAt, List.map_map]
    refine List.map_congr_left fun j hj => ?_
    have := List.mem_range.mp hj
    simp only [Function.comp, show 4 * k + j < D by omega, ite_true, Offset.add_add]
  · rw [show List.replicate 4 c = (List.range 4).map fun _ => c from rfl]
    refine List.map_congr_left fun j hj => ?_
    have := List.mem_range.mp hj
    simp only [Function.comp, show ¬ 4 * k + j < D by omega, ite_false]

/-- All `B` bytes: `K₀ ⊕ c`, for a key of `D ≤ B` bytes. -/
theorem padBytes_eq (m : Mem) (K : Addr) {D : Nat} (c : Byte) (H : Spec.Hmac.HashFunction)
    (hD : D ≤ H.blockSize) :
    padBytes m K D c H.blockSize = xorPad (blockKey H (bytesAt m K D)) c := by
  rw [Proof.Pbkdf2.MdKeys.blockKey_short H (by simp only [bytesAt_length]; exact hD)]
  apply List.ext_getElem (by simp [padBytes, xorPad, bytesAt_length]; omega)
  intro i h₁ h₂
  simp only [padBytes, List.getElem_map, List.getElem_range, xorPad]
  by_cases hi : i < D
  · rw [List.getElem_append_left (by simp [bytesAt_length, hi])]
    simp [hi, bytesAt]
  · simp only [hi, ite_false]
    rw [List.getElem_append_right (by simp [bytesAt_length]; omega)]
    simp

/-- The value `padWord b` leaves in `t5`. -/
def padVal (b : Nat) : BitVec 64 :=
  (BitVec.ofNat 64 b ||| BitVec.ofNat 64 b <<< 8) ||| (BitVec.ofNat 64 b ||| BitVec.ofNat 64 b <<< 8) <<< 16

theorem padVal_ipad : (padVal 0x36).setWidth 32 = ipad ++ ipad ++ ipad ++ ipad := by decide
theorem padVal_opad : (padVal 0x5c).setWidth 32 = opad ++ opad ++ opad ++ opad := by decide

/-- The pad's word into `t5`, through `t4`. -/
theorem padWord_ok {b : Nat} (hb : b < 2048) {t : State} {rest : List Instr} {Q : State → Prop}
    (k : ∀ t', t'.mem = t.mem → t'.rd = t.rd → t'.wr = t.wr → t'.sp = t.sp →
      (∀ r, r ≠ .t4 → r ≠ .t5 → t'.gpr r = t.gpr r) → t'.gpr .t5 = padVal b → WP isa (.block rest) t' Q) :
    WP isa (.block (padWord b ++ rest)) t Q := by
  simp only [padWord, List.cons_append, List.nil_append]
  refine wp_li hb fun t₁ u₁ => wp_sll (by decide) fun t₂ u₂ => wp_or fun t₃ u₃ =>
    wp_sll (by decide) fun t₄ u₄ => wp_or fun t₅ u₅ => k t₅ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]
  · intro r h4 h5
    rw [u₅.other r h5, u₄.other r h4, u₃.other r h5, u₂.other r h4, u₁.other r h5]
  · rw [u₅.gpr, u₄.gpr, u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₂.other _ (by decide), u₁.gpr]
    rfl

section
variable {P : Rfc} {s₀ : State} (hp : Pre P s₀)
include hp

/-- Word `k` of the padded key, after `4 k` of its bytes. -/
theorem padW_ok {t : State} (c : Byte) {k : Nat} (hD : P.c.D % 4 = 0) (hk : 4 * k + 4 ≤ P.c.B)
    {u : State} (hk' : KR P s₀ u) (hcx : (u.gpr .t5).setWidth 32 = c ++ c ++ c ++ c)
    (hm : u.mem = writeBytes t.mem (cA s₀ sPad) (padBytes t.mem (sA s₀ fK) P.c.D c (4 * k)))
    (hKd : k < P.c.D / 4 → bytesAt u.mem (sA s₀ fK + BitVec.ofNat 64 (4 * k)) 4 =
      bytesAt t.mem (sA s₀ fK + BitVec.ofNat 64 (4 * k)) 4) :
    WP isa (.block (P.c.padW k)) u fun u' => u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp ∧
      (∀ r, r ≠ .t1 → u'.gpr r = u.gpr r) ∧
      u'.mem = writeBytes t.mem (cA s₀ sPad) (padBytes t.mem (sA s₀ fK) P.c.D c (4 * k + 4)) := by
  have hz := sizes P
  have hzH := hz.H
  have hzQ := hz.Q
  obtain ⟨hD1, hD2⟩ := hz.D
  have hB := hz.B
  have hl := padBytes_length t.mem (sA s₀ fK) P.c.D c (4 * k)
  have hap : ∀ ys : List Byte, ys.length = 4 →
      writeBytes (writeBytes t.mem (cA s₀ sPad) (padBytes t.mem (sA s₀ fK) P.c.D c (4 * k)))
        (cA s₀ sPad + BitVec.ofNat 64 (4 * k)) ys =
        writeBytes t.mem (cA s₀ sPad) (padBytes t.mem (sA s₀ fK) P.c.D c (4 * k) ++ ys) := fun ys hys => by
    have := writeBytes_append t.mem (cA s₀ sPad) (padBytes t.mem (sA s₀ fK) P.c.D c (4 * k)) ys
      (by rw [hl, hys]; omega)
    rwa [hl] at this
  have hst : u.gpr .s0 + BitVec.ofNat 64 (sPad + 4 * k) = cA s₀ sPad + BitVec.ofNat 64 (4 * k) := by
    rw [hk'.s0, Offset.add_add]
  have hal : (cA s₀ sPad + BitVec.ofNat 64 (4 * k)).toNat % 4 = 0 := by
    rw [Offset.add_add, BitVec.toNat_add, BitVec.toNat_ofNat]
    have := hp.ca; have := hp.nc; simp only [sPad]; omega
  have hw : InRegions u.wr (cA s₀ sPad + BitVec.ofNat 64 (4 * k)) 4 := by
    rw [Offset.add_add]
    exact ⟨scrR s₀, scr_wr hp hk'.wr, Offset.contains_base _ (by simp only [sPad]; omega) (by have := hp.nc; simp only [sPad]; omega)⟩
  have sw : ∀ x : BitVec 32, (x.setWidth 64).setWidth 32 = x := fun x => by
    rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]
  by_cases hkD : k < P.c.D / 4
  · rw [Cfg.padW, ite_eq_left_of_eq_true _ _ (eq_true hkD)]
    have hKa : u.gpr .s1 + BitVec.ofNat 64 (fK + 4 * k) = sA s₀ fK + BitVec.ofNat 64 (4 * k) := by
      rw [hk'.s1, Offset.add_add]
    refine wp_lwu (a := sA s₀ fK + BitVec.ofNat 64 (4 * k)) (by simp only [fK]; omega) hKa (by
        rw [Offset.add_add, BitVec.toNat_add, BitVec.toNat_ofNat]
        have := hp.al; have := hp.top; simp only [fK]; omega)
      (by rw [Offset.add_add]; exact in_fr' hp hk'.wr (by simp only [fK]; omega)) fun s₁ u₁ => ?_
    refine wp_xor fun s₂ u₂ => ?_
    refine wp_sw (a := cA s₀ sPad + BitVec.ofNat 64 (4 * k)) (by simp only [sPad]; omega)
      (by rw [u₂.other _ (by decide), u₁.other _ (by decide), hst]) hal
      (by rw [u₂.wr, u₁.wr]; exact hw) fun s₃ m₃ => WP.block_nil ?_
    refine ⟨by rw [m₃.rd, u₂.rd, u₁.rd], by rw [m₃.wr, u₂.wr, u₁.wr], by rw [m₃.sp, u₂.sp, u₁.sp],
      fun r hr => by rw [m₃.gpr, u₂.other r hr, u₁.other r hr], ?_⟩
    rw [m₃.mem, u₂.mem, u₁.mem, u₂.gpr, u₁.gpr, u₁.other .t5 (by decide), BitVec.setWidth_xor, sw, hcx,
      Proof.Pbkdf2.MdKeys.writeW_xorRep, hKd hkD, hm, hap _ (by simp [bytesAt_length]),
      padBytes_succ _ _ _ hD, ite_eq_left_of_eq_true _ _ (eq_true hkD)]
  · rw [Cfg.padW, ite_eq_right_of_eq_false _ _ (eq_false hkD)]
    refine wp_sw (a := cA s₀ sPad + BitVec.ofNat 64 (4 * k)) (by simp only [sPad]; omega) hst hal hw
      fun s₃ m₃ => WP.block_nil ?_
    refine ⟨m₃.rd, m₃.wr, m₃.sp, fun r _ => by rw [m₃.gpr], ?_⟩
    rw [m₃.mem, hcx, Proof.Pbkdf2.MdKeys.writeW_rep, hm, hap _ (by simp), padBytes_succ _ _ _ hD,
      ite_eq_right_of_eq_false _ _ (eq_false hkD)]

/-- The first `k` words of the padded key, from the state `u`. -/
theorem padWs_ok (c : Byte) (hD : P.c.D % 4 = 0) :
    ∀ k, 4 * k ≤ P.c.B → ∀ u : State, KR P s₀ u → (u.gpr .t5).setWidth 32 = c ++ c ++ c ++ c →
      WP isa (.block ((List.range k).flatMap P.c.padW)) u fun u' => u'.rd = u.rd ∧ u'.wr = u.wr ∧
        u'.sp = u.sp ∧ (∀ r, r ≠ .t1 → u'.gpr r = u.gpr r) ∧
        u'.mem = writeBytes u.mem (cA s₀ sPad) (padBytes u.mem (sA s₀ fK) P.c.D c (4 * k))
  | 0, _, u, _, _ => WP.block_nil ⟨rfl, rfl, rfl, fun _ _ => rfl, by simp [padBytes, writeBytes_nil]⟩
  | k + 1, hk, u, hk', hcx => by
    have hz := sizes P
    have hB := hz.B
    have hzH := hz.H
    have hzQ := hz.Q
    obtain ⟨hD1, hD2⟩ := hz.D
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (padWs_ok c hD k (by omega) u hk' hcx) fun u₁ ⟨hrd₁, hwr₁, hsp₁, hg₁, hm₁⟩ => ?_
    have hf : Frame [cR s₀ sPad P.c.B] u.mem u₁.mem := by
      rw [hm₁]; exact writeBytes_frame _ _ _ (by
        rw [padBytes_length]
        have := Offset.contains_base (cA s₀ sPad) (d := 0) (n := 4 * k) (k := P.c.B) (by omega) (by omega)
        rwa [BitVec.add_zero] at this)
    have hk₁ : KR P s₀ u₁ := hk'.keep hrd₁ hwr₁ hsp₁ (fun r hr => hg₁ r (by revert r; decide)) hf
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.f_c.sub_left (part_sub (by have := (sizes P).Q; have := (sizes P).H; omega))).sub_right
          (scr_sub (by simp only [sPad]; omega)))
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨scrR s₀, by simp, scr_sub (by simp only [sPad]; omega)⟩)
    refine WP.mono (padW_ok hp (t := u) c (k := k) hD (by omega) hk₁ (by rw [hg₁ _ (by decide), hcx]) hm₁
      (fun hkD => Proof.Sha256.Stream.bytesAt_congr fun i hi => hf.bytes (R := ⟨sA s₀ fK + BitVec.ofNat 64 (4 * k), 4⟩)
        (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          rw [Offset.add_add]
          exact (hp.f_c.sub_left (part_sub (by simp only [fK]; omega))).sub_right
            (scr_sub (by simp only [sPad]; omega))) (by show 4 ≤ 2 ^ 64; omega) hi))
      fun u₂ ⟨hrd₂, hwr₂, hsp₂, hg₂, hm₂⟩ => ⟨hrd₂.trans hrd₁, hwr₂.trans hwr₁, hsp₂.trans hsp₁,
        fun r hr' => (hg₂ r hr').trans (hg₁ r hr'), by rw [hm₂, show 4 * (k + 1) = 4 * k + 4 by omega]⟩

/-- `K₀ ⊕ c` at `scratch + sPad`, with `c`'s word set by `padWord b`. -/
theorem padBlk_ok {s t : State} (h : St P s₀ s t) (hD : P.c.D % 4 = 0) {b : Nat} (hb : b < 2048) {c : Byte}
    (hc : (padVal b).setWidth 32 = c ++ c ++ c ++ c) :
    WP isa (.block (P.c.padBlk (padWord b))) t fun u => St P s₀ s u ∧
      Frame [cR s₀ sPad P.c.B] t.mem u.mem ∧
      bytesAt u.mem (cA s₀ sPad) P.c.B = xorPad (k0Of P s₀ s.mem) c := by
  have hz := sizes P
  have hzH := hz.H
  have hzQ := hz.Q
  obtain ⟨hD1, hD2⟩ := hz.D
  have hB := hz.B
  rw [Cfg.padBlk]
  refine padWord_ok hb fun t₁ hm₁ hrd₁ hwr₁ hsp₁ hg₁ h5 => ?_
  have k₁ : KR P s₀ t₁ := h.kr.same hrd₁ hwr₁ hsp₁ (fun r hr => hg₁ r (by revert r hr; decide)
    (by revert r hr; decide)) hm₁
  refine WP.mono (padWs_ok hp c hD (P.c.B / 4) (by omega) t₁ k₁ (by rw [h5]; exact hc))
    fun u ⟨hrd, hwr, hsp, hg, hm⟩ => ?_
  have e4 : 4 * (P.c.B / 4) = P.c.B := by omega
  rw [e4, hm₁] at hm
  have hf : Frame [cR s₀ sPad P.c.B] t.mem u.mem := by
    rw [hm]; exact writeBytes_frame _ _ _ (by
      rw [padBytes_length]
      have := Offset.contains_base (cA s₀ sPad) (d := 0) (n := P.c.B) (k := P.c.B) (by omega) (by omega)
      rwa [BitVec.add_zero] at this)
  have hsub : Region.Sub (cR s₀ sPad P.c.B) (stR s₀) := st_sub (by simp only [sPad]; omega)
  refine ⟨⟨h.kr.keep (hrd.trans hrd₁) (hwr.trans hwr₁) (hsp.trans hsp₁)
      (fun r hr => (hg r (by revert r; decide)).trans (hg₁ r (by revert r hr; decide) (by revert r hr; decide))) hf
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.f_c.sub_left (part_sub (by have := (sizes P).Q; have := (sizes P).H; omega))).sub_right
          (scr_sub (by simp only [sPad]; omega)))
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨scrR s₀, by simp, scr_sub (by simp only [sPad]; omega)⟩),
    h.fr.trans (hf.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, hsub⟩),
    fun r hr => (hg r (by revert r hr; decide)).trans
      ((hg₁ r (by revert r hr; decide) (by revert r hr; decide)).trans (h.pr r hr))⟩, hf, ?_⟩
  rw [hm, Proof.Hmac.Generic.Common.bytesAt_writeBytes_self' (padBytes_length _ _ _ _ _) (by omega),
    show P.c.B = P.hH.SH.H.blockSize by rw [P.hH.hB, hz.DB.2.1],
    padBytes_eq _ _ _ _ (by rw [P.hH.hB, hz.DB.2.1]; omega)]
  exact congrArg (fun x => xorPad (blockKey P.hH.SH.H x) c) (h.key hp)

end

/-! ## HMAC -/

/-- After `hinit`: the states of the key. -/
def HK (P : Rfc) (s₀ s t : State) : Prop :=
  St P s₀ s t ∧ t.syms = s₀.syms ∧ P.hH.SH.Repr t.mem (cA s₀ sIn) (xorPad (k0Of P s₀ s.mem) ipad) ∧
    P.hH.SH.Repr t.mem (cA s₀ sOut) (xorPad (k0Of P s₀ s.mem) opad)

/-- After the parts `pre` were absorbed. -/
def HU (P : Rfc) (s₀ s : State) (pre : List Byte) (t : State) : Prop :=
  St P s₀ s t ∧ t.syms = s₀.syms ∧ P.hH.SH.Repr t.mem (cA s₀ sIn) (xorPad (k0Of P s₀ s.mem) ipad ++ pre) ∧
    P.hH.SH.Repr t.mem (cA s₀ sOut) (xorPad (k0Of P s₀ s.mem) opad)

/-- After an HMAC: the MAC at `dst`, and memory changed only in HMAC's
working space, the MAC and the stack below the frame. -/
def HD (P : Rfc) (s₀ s : State) (msg : List Byte) (dst : Nat) (t : State) : Prop :=
  KR P s₀ t ∧ t.syms = s₀.syms ∧ bytesAt t.mem (sA s₀ dst) P.c.D = Spec.Hmac.hmac P.hH.SH.H (kOf P s₀ s.mem) msg ∧
    Frame [stR s₀, sR s₀ dst P.c.D, stk P s₀] s.mem t.mem ∧ ∀ r ∈ preserved, t.gpr r = s.gpr r

section
variable {P : Rfc} {s₀ : State} (hp : Pre P s₀)
include hp

/-- The states are apart from what writes the other state, the padded key
or the inner digest, and the stack below the frame. -/
theorem st_apart {o o' n : Nat} (ho : o + P.H.S ≤ 384) (hd : o + P.H.S ≤ o' ∨ o' + n ≤ o) (hn : o' + n ≤ 576) :
    ∀ r ∈ [cR s₀ o' n, below s₀.sp P.X], Region.Disjoint (cR s₀ o P.H.S) r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact scr_disj hp hd (by omega) (by omega)
  · exact (hp.b_c.sub_left (below_stk hp (Nat.le_refl _))).symm.sub_left (scr_sub (by omega))

theorem hinit_ok {s : State} (h : KR P s₀ s) (hsy : s.syms = s₀.syms) (hD : P.c.D % 4 = 0) :
    WP isa P.c.hinit s (HK P s₀ s) := by
  have hz := sizes P
  have hS := hz.S192
  have hB := hz.B
  have hl := blockKey_length P (kOf P s₀ s.mem)
  unfold Cfg.hinit
  refine WP.seq (WP.mono (initCall_ok hp (St.refl h) hsy (o := sIn) (by simp only [sIn]; omega))
    fun t₁ ⟨S₁, y₁, r₁, _⟩ => ?_)
  refine WP.seq (WP.mono (initCall_ok hp S₁ y₁ (o := sOut) (by simp only [sOut]; omega))
    fun t₂ ⟨S₂, y₂, r₂, f₂⟩ => ?_)
  have r₁' := repr_keep f₂ (st_apart hp (o := sIn) (o' := sOut) (by simp only [sIn]; omega)
    (.inl (by simp only [sIn, sOut]; omega)) (by simp only [sOut]; omega)) r₁
  refine WP.seq (WP.of_syms (WP.mono (padBlk_ok hp S₂ hD (b := 0x36) (by decide) padVal_ipad)
    fun t₃ ⟨S₃, f₃, p₃⟩ y₃ => ?_))
  have d₃ : ∀ {o}, o + P.H.S ≤ 384 → ∀ r ∈ [cR s₀ sPad P.c.B], Region.Disjoint (cR s₀ o P.H.S) r :=
    fun ho r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact scr_disj hp (.inl (by simp only [sPad]; omega)) (by omega) (by simp only [sPad]; omega)
  have r₁₃ := repr_keep f₃ (d₃ (o := sIn) (by simp only [sIn]; omega)) r₁'
  have r₂₃ := repr_keep f₃ (d₃ (o := sOut) (by simp only [sOut]; omega)) r₂
  refine WP.seq (WP.mono (updCall_ok hp S₃ (y₃.trans y₂) (o := sIn) (cnt := 0) (by simp only [sIn]; omega)
    (by decide) (base := .s0) (off := sPad) (len := P.c.B) (.inr ⟨rfl, Nat.le_refl _, by simp only [sPad]; omega⟩))
    fun t₄ ⟨S₄, y₄, u₄, f₄⟩ => ?_)
  have r₁₄ := u₄ [] r₁₃ rfl
  rw [List.nil_append, show pA s₀ (.s0, sPad, P.c.B) = cA s₀ sPad from rfl, p₃] at r₁₄
  have r₂₄ := repr_keep f₄ (st_apart hp (o := sOut) (o' := sIn) (by simp only [sOut]; omega)
    (.inr (by simp only [sIn, sOut]; omega)) (by simp only [sIn]; omega)) r₂₃
  refine WP.seq (WP.of_syms (WP.mono (padBlk_ok hp S₄ hD (b := 0x5c) (by decide) padVal_opad)
    fun t₅ ⟨S₅, f₅, p₅⟩ y₅ => ?_))
  have r₁₅ := repr_keep f₅ (d₃ (o := sIn) (by simp only [sIn]; omega)) r₁₄
  have r₂₅ := repr_keep f₅ (d₃ (o := sOut) (by simp only [sOut]; omega)) r₂₄
  refine WP.mono (updCall_ok hp S₅ (y₅.trans y₄) (o := sOut) (cnt := 0) (by simp only [sOut]; omega)
    (by decide) (base := .s0) (off := sPad) (len := P.c.B) (.inr ⟨rfl, Nat.le_refl _, by simp only [sPad]; omega⟩))
    fun t₆ ⟨S₆, y₆, u₆, f₆⟩ => ?_
  have r₂₆ := u₆ [] r₂₅ rfl
  rw [List.nil_append, show pA s₀ (.s0, sPad, P.c.B) = cA s₀ sPad from rfl, p₅] at r₂₆
  have r₁₆ := repr_keep f₆ (st_apart hp (o := sIn) (o' := sOut) (by simp only [sIn]; omega)
    (.inl (by simp only [sIn, sOut]; omega)) (by simp only [sOut]; omega)) r₁₅
  exact ⟨S₆, y₆, r₁₆, r₂₆⟩

omit hp in
theorem HK.hu {s t : State} (h : HK P s₀ s t) : HU P s₀ s [] t := by
  obtain ⟨a, y, b, c⟩ := h
  exact ⟨a, y, by rw [List.append_nil]; exact b, c⟩

/-- The parts absorbed, one `update` each. -/
theorem upds_ok {s : State} : ∀ (ps : List Part) {t : State} {pre : List Byte}, HU P s₀ s pre t →
    (∀ p ∈ ps, PartOk P p) → P.c.B + pre.length + total ps < 2048 →
    WP isa (P.c.upds pre.length ps) t (HU P s₀ s (pre ++ msgOf s.mem s₀ ps))
  | [], t, pre, h, _, _ => WP.block_nil (by rw [msgOf, List.append_nil]; exact h)
  | p :: ps, t, pre, h, hps, hb => by
    have hz := sizes P
    have hS := hz.S192
    have hpo : PartOk P p := hps p (by simp)
    have hl : p.2.2 ≤ total (p :: ps) := by simp only [total]; omega
    have hK := blockKey_length P (kOf P s₀ s.mem)
    unfold Cfg.upds
    obtain ⟨b, o, n⟩ := p
    refine WP.seq (WP.mono (updCall_ok hp h.1 h.2.1 (o := sIn) (cnt := P.c.B + pre.length)
      (by simp only [sIn]; omega) (by omega) (base := b) (off := o) (len := n) (.inl hpo))
      fun t₂ ⟨S₂, y₂, u₂, f₂⟩ => ?_)
    have e₁ := u₂ _ h.2.2.1 (by rw [List.length_append, xorPad_length, hK])
    rw [List.append_assoc, h.1.part hp hpo] at e₁
    have h₂ : HU P s₀ s (pre ++ bytesAt s.mem (pA s₀ (b, o, n)) n) t₂ :=
      ⟨S₂, y₂, e₁, repr_keep f₂ (st_apart hp (o := sOut) (o' := sIn) (by simp only [sOut]; omega)
        (.inr (by simp only [sIn, sOut]; omega)) (by simp only [sIn]; omega)) h.2.2.2⟩
    have e : pre.length + n = (pre ++ bytesAt s.mem (pA s₀ (b, o, n)) n).length := by
      rw [List.length_append, bytesAt_length]
    rw [e]
    refine WP.mono (upds_ok ps h₂ (fun q hq => hps q (by simp [hq])) (by
      rw [List.length_append, bytesAt_length]; simp only [total] at hb; omega)) fun t₃ h₃ => ?_
    rwa [List.append_assoc, ← msgOf.eq_2] at h₃

omit hp in
theorem hash_length (m : List Byte) : (P.hH.SH.H.hash m).length = P.c.D := by
  rw [P.hH.hashLen, (sizes P).DB.1]

/-- The MAC, for the message `msg`, to the frame at `dst`. -/
theorem hfin_ok {s t : State} {msg : List Byte} (h : HU P s₀ s msg t) {dst : Nat}
    (hdst : 64 ≤ dst ∧ dst + P.c.D ≤ P.c.frB) (hm : P.c.B + msg.length < 2048) :
    WP isa (P.c.hfin msg.length dst) t (HD P s₀ s msg dst) := by
  have hz := sizes P
  have hS := hz.S192
  have hB := hz.B
  obtain ⟨hD1, hD2⟩ := hz.D
  have hK := blockKey_length P (kOf P s₀ s.mem)
  obtain ⟨S, y, ri, ro⟩ := h
  unfold Cfg.hfin
  refine WP.seq (WP.mono (finCall_ok hp S.kr y (o := sIn) (cnt := P.c.B + msg.length) (by simp only [sIn]; omega)
    hm (base := .s0) (off := sTmp) (.inl ⟨rfl, rfl⟩)) fun t₁ ⟨k₁, y₁, p₁, d₁, f₁⟩ => ?_)
  have hd₁ := d₁ _ ri (by rw [List.length_append, xorPad_length, hK]; omega)
    (by rw [List.length_append, xorPad_length, hK])
  have hw₁ : ∀ r ∈ [cR s₀ sIn P.H.S, ⟨pA s₀ (.s0, sTmp, P.c.D), P.c.D⟩, below s₀.sp P.X],
      ∃ r' ∈ [stR s₀, stk P s₀], Region.Sub r r' := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, by simp, st_sub (by simp only [sIn]; omega)⟩
    · exact ⟨_, by simp, st_sub (o := sTmp) (n := P.c.D) (by simp only [sTmp]; omega)⟩
    · exact ⟨_, by simp, fun x hx => hx⟩
  have S₁ : St P s₀ s t₁ := ⟨k₁, S.fr.trans (f₁.sub hw₁), fun r hr => (p₁ r hr).trans (S.pr r hr)⟩
  have ro₁ := repr_keep f₁ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (in_out hp).symm
    · exact scr_disj hp (a := sOut) (b := sTmp) (.inl (by simp only [sOut, sTmp]; omega)) (by simp only [sOut]; omega)
        (by simp only [sTmp]; omega)
    · exact ((st_apart hp (o := sOut) (o' := sIn) (n := 0) (by simp only [sOut]; omega)
        (.inr (by simp only [sIn, sOut]; omega)) (by simp only [sIn]; omega)) _ (by simp))) ro
  refine WP.seq (WP.mono (updCall_ok hp S₁ y₁ (o := sOut) (cnt := P.c.B) (by simp only [sOut]; omega)
    (by omega) (base := .s0) (off := sTmp) (len := P.c.D) (.inr ⟨rfl, by simp only [sTmp]; omega,
      by simp only [sTmp]; omega⟩)) fun t₂ ⟨S₂, y₂, u₂, f₂⟩ => ?_)
  have ro₂ := u₂ _ ro₁ (by rw [xorPad_length, hK])
  rw [hd₁] at ro₂
  refine WP.mono (finCall_ok hp S₂.kr y₂ (o := sOut) (cnt := P.c.B + P.c.D) (by simp only [sOut]; omega)
    (by omega) (base := .s1) (off := dst) (.inr ⟨rfl, hdst⟩)) fun t₃ ⟨k₃, y₃, p₃, d₃, f₃⟩ => ?_
  have hd₃ := d₃ _ ro₂ (by rw [List.length_append, xorPad_length, hK, hash_length]; omega)
    (by rw [List.length_append, xorPad_length, hK, hash_length])
  refine ⟨k₃, y₃, ?_, ?_, fun r hr => (p₃ r hr).trans (S₂.pr r hr)⟩
  · exact hd₃
  · refine (S₂.fr.sub fun r hr => ?_).trans (f₃.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨stR s₀, by simp, fun x hx => hx⟩
      · exact ⟨stk P s₀, by simp, fun x hx => hx⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨stR s₀, by simp, st_sub (by simp only [sOut]; omega)⟩
      · exact ⟨sR s₀ dst P.c.D, by simp, fun x hx => hx⟩
      · exact ⟨stk P s₀, by simp, fun x hx => hx⟩

/-- `HMAC_K(parts)` to `dst`. -/
theorem hmac_ok {s : State} (h : KR P s₀ s) (hsy : s.syms = s₀.syms) (hD : P.c.D % 4 = 0)
    {ps : List Part} (hps : ∀ p ∈ ps, PartOk P p)
    (hb : P.c.B + total ps < 2048) {dst : Nat} (hdst : 64 ≤ dst ∧ dst + P.c.D ≤ P.c.frB) :
    WP isa (P.c.hmac ps dst) s (HD P s₀ s (msgOf s.mem s₀ ps) dst) := by
  unfold Cfg.hmac
  refine WP.seq (WP.mono (hinit_ok hp h hsy hD) fun t₂ h₂ => ?_)
  refine WP.seq (WP.mono (upds_ok hp ps (pre := []) h₂.hu hps (by simpa using hb)) fun t₃ h₃ => ?_)
  rw [List.nil_append] at h₃
  have hl := msgOf_length s.mem s₀ ps
  rw [← hl]
  exact hfin_ok hp h₃ hdst (by omega)

end

end VG.Proof.Ecdsa.Rfc6979.RISCV64
