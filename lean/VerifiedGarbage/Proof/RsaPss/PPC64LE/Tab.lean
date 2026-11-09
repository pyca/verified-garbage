module

public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.MgfT
public import VerifiedGarbage.Impl.RsaPss.PPC64LE
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms

/-!
# RSASSA-PSS on PPC64LE: the hash function's table

Untrusted: everything here is checked by Lean. The hash function's table,
of the interface `MdHash`, that is our stack argument `j`, as on entry
(`MdTabS`: the argument and the table's eleven words readable and apart
from what we write, its words 0 to 4 the addresses of the streaming
`init`, `update` and `finalize` of `H`, of the compression function `cn`
and of the digest `dn`, and an indirect call of `f`'s functions to them
reaching their code, `MdTabOK`). A load of one of its words (`wp_twordM`),
and the calls of `init`, `update` and `finalize` through it (`initM_ok`,
`updM_ok`, `finM_ok`), which run as `H`'s.
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE
open VG.Impl.RsaPss.PPC64LE (MdFns)
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)
open VG.Proof.RsaOaep.PPC64LE (Base Fits SC kR cR off Same TabMem init_ok upd_ok fin_ok not_r12)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only wp_addSp wp_ld wp_nil)

/-- An indirect call of `f`'s functions, at the addresses `sy` gives, to the
address of one of `H`'s streaming functions, of the compression function
`cn` (of code `cc`) or of the digest `dn` (of code `dc`) reaches it. -/
structure MdTabOK (H : Hash) (cn : String) (cc : Prog isa) (dn : String) (dc : Prog isa) (f : MdFns)
    (sy : String → Addr) : Prop where
  i : f.init.find? (fun q => sy q.1 == sy H.initN) = some (H.initN, H.initC)
  u : f.upd.find? (fun q => sy q.1 == sy H.updN) = some (H.updN, H.updC)
  fz : f.fin.find? (fun q => sy q.1 == sy H.finN) = some (H.finN, H.finC)
  c : f.comp.find? (fun q => sy q.1 == sy cn) = some (cn, cc)
  d : f.dig.find? (fun q => sy q.1 == sy dn) = some (dn, dc)

/-- The table of `MdHash` at `p` that is our stack argument `j`, as on
entry `s`. -/
structure MdTabS (H : Hash) (cn : String) (cc : Prog isa) (dn : String) (dc : Prog isa) (f : MdFns) (j : Nat)
    (S : State → Addr) (s : State) (p : Addr) : Prop where
  jo : arg j < 2 ^ 15 ∧ arg j % 4 = 0
  arg : s.mem.readW (stackArgAddr s j) 64 = p
  argR : InRegions s.rd (stackArgAddr s j) 8
  argK : Region.Disjoint ⟨stackArgAddr s j, 8⟩ (kR s)
  argS : Region.Disjoint ⟨stackArgAddr s j, 8⟩ (SC S s)
  tR : ∀ k < 11, InRegions s.rd (p + BitVec.ofNat 64 (8 * k)) 8
  tK : ∀ k < 11, Region.Disjoint ⟨p + BitVec.ofNat 64 (8 * k), 8⟩ (kR s)
  tS : ∀ k < 11, Region.Disjoint ⟨p + BitVec.ofNat 64 (8 * k), 8⟩ (SC S s)
  mem : TabMem H s.syms p s.mem
  mc : s.mem.readW (p + BitVec.ofNat 64 24) 64 = s.syms cn
  md : s.mem.readW (p + BitVec.ofNat 64 32) 64 = s.syms dn
  ok : MdTabOK H cn cc dn dc f s.syms

variable {H : Hash} {cn dn : String} {cc dc : Prog isa} {f : MdFns} {j : Nat}

/-- `MdTabS` of a state with `s`'s stack pointer, regions, statics' addresses
and working space, and memory as `s`'s apart from regions disjoint from the
stack argument and the table. -/
theorem MdTabS.transfer {S S' : State → Addr} {s s' : State} {p : Addr}
    (T : MdTabS H cn cc dn dc f j S s p) (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd) (hsy : s'.syms = s.syms)
    (hS : SC S' s' = SC S s) {rs : List Region} (hm : Frame rs s.mem s'.mem)
    (ha : ∀ r ∈ rs, Region.Disjoint ⟨stackArgAddr s j, 8⟩ r)
    (ht : ∀ k < 11, ∀ r ∈ rs, Region.Disjoint ⟨p + BitVec.ofNat 64 (8 * k), 8⟩ r) :
    MdTabS H cn cc dn dc f j S' s' p := by
  have eA : stackArgAddr s' j = stackArgAddr s j := by simp only [stackArgAddr, hsp]
  have eK : kR s' = kR s := by simp only [kR, hsp]
  have rd : ∀ k < 11, s'.mem.readW (p + BitVec.ofNat 64 (8 * k)) 64 = s.mem.readW (p + BitVec.ofNat 64 (8 * k)) 64 :=
    fun k hk => hm.readW (w := 64) (Region.contains_self _ _) (ht k hk) (by decide)
  obtain ⟨m0, m1, m2⟩ := T.mem
  have r0 := rd 0 (by decide)
  rw [show p + BitVec.ofNat 64 (8 * 0) = p by simp] at r0
  refine ⟨T.jo, ?_, by rw [hrd, eA]; exact T.argR, by rw [eA, eK]; exact T.argK, by rw [eA, hS]; exact T.argS,
    fun k hk => by rw [hrd]; exact T.tR k hk, fun k hk => by rw [eK]; exact T.tK k hk,
    fun k hk => by rw [hS]; exact T.tS k hk, ⟨?_, ?_, ?_⟩, ?_, ?_, by rw [hsy]; exact T.ok⟩
  · rw [eA, hm.readW (w := 64) (Region.contains_self _ _) ha (by decide)]; exact T.arg
  · rw [hsy, r0]; exact m0
  · rw [hsy, rd 1 (by decide)]; exact m1
  · rw [hsy, rd 2 (by decide)]; exact m2
  · rw [hsy, rd 3 (by decide)]; exact T.mc
  · rw [hsy, rd 4 (by decide)]; exact T.md

/-- The table's word `k` into `d`, through our stack argument `j`. -/
theorem wp_twordM {S : State → Addr} {vf : State → Reg → BitVec 64} {s t : State} {p : Addr}
    (T : MdTabS H cn cc dn dc f j S s p) (h : Base S vf s t) {k : Nat} (hk : k < 11) {d : Reg} (hd : d ≠ .r0)
    {is : List Instr} {Q : State → Prop}
    (kk : ∀ t', Only [d] t t' → t'.gpr d = s.mem.readW (p + BitVec.ofNat 64 (8 * k)) 64 → WP isa (.block is) t' Q) :
    WP isa (.block (tword d j k ++ is)) t Q := by
  simp only [tword, List.cons_append, List.nil_append]
  refine wp_addSp fun u₁ o₁ e₁ => wp_ld (a := stackArgAddr s j) (by
      rw [e₁, h.sp, BitVec.add_zero, VG.Proof.RsaOaep.PPC64LE.stackArgAddr_fb])
    (by rw [o₁.rd, h.rd]; exact let ⟨R, hR, hc⟩ := T.argR; ⟨R, List.mem_append_left _ hR, hc⟩)
    (fun u₂ o₂ e₂ => wp_ld (a := p + BitVec.ofNat 64 (8 * k))
      (by rw [e₂, o₁.mem, h.readW_apart T.argK T.argS, T.arg])
      (by rw [o₂.rd, o₁.rd, h.rd]; exact let ⟨R, hR, hc⟩ := T.tR k hk; ⟨R, List.mem_append_left _ hR, hc⟩)
      (fun u₃ o₃ e₃ => kk u₃ ((o₁.trans (o₂.trans o₃)).mono fun r hr => by
        simp only [List.mem_append, List.mem_singleton, or_self] at hr ⊢; exact hr) (by
        rw [e₃, o₂.mem, o₁.mem, h.readW_apart (T.tK k hk) (T.tS k hk)])) hd (by omega)) hd T.jo

/-- The call of the table's function `k`, among `ts`, which reaches `n`, as
the call of `n` from the state the load of its address leaves. -/
theorem tcallM_ok {S : State → Addr} {vf : State → Reg → BitVec 64} {s t : State} {p : Addr}
    (T : MdTabS H cn cc dn dc f j S s p) (h : Base S vf s t) (sy : t.syms = s.syms) {k : Nat} (hk : k < 5)
    {ts : List (String × Prog isa)} {n : String} {c : Prog isa}
    (hf : ts.find? (fun q => s.syms q.1 == s.syms n) = some (n, c))
    (hw : s.mem.readW (p + BitVec.ofNat 64 (8 * k)) 64 = s.syms n) {Q : State → Prop}
    (kk : ∀ t', Only [.r12] t t' → t'.syms = t.syms → WP isa (.call n c) t' Q) : WP isa (tcall j k ts) t Q := by
  show WP isa (.seq (.block (tword .r12 j k ++ [])) (Code.icalls .bctrl ts)) t Q
  refine WP.seq (WP.of_syms (wp_twordM T h (by omega) (by decide) fun t' o e => wp_nil fun sy' => ?_))
  refine WP.icalls_of_call (a := t'.gpr .r12) rfl ?_ (kk t' o sy')
  show ts.find? (fun q => t'.syms q.1 == t'.gpr .r12) = _
  rw [e, hw, sy', sy]; exact hf

section
variable {S : State → Addr} {vf : State → Reg → BitVec 64} {s : State} (P : Fits S s) {p : Addr}
  (T : MdTabS H cn cc dn dc f j S s p)
include P T

/-- `init` through the table. -/
theorem initM_ok (hH : HashOK H) {t : State} (h : Base S vf s t) (sy : t.syms = s.syms)
    (h3 : t.gpr .r3 = off (S s) oSt) :
    WP isa (tcall j 0 f.init) t fun t' => (Base S vf s t' ∧ (∀ r ∈ preserved, t'.gpr r = t.gpr r) ∧
      Same (S s) t t' [(oSt, H.S)] ∧ hH.SH.Repr t'.mem (off (S s) oSt) []) ∧ t'.syms = s.syms :=
  tcallM_ok T h sy (k := 0) (by decide) T.ok.i (by rw [Nat.mul_zero, BitVec.add_zero]; exact T.mem.1)
    fun t' o sy' => WP.mono_syms (init_ok P hH (h.only P o) (by rw [o.get .r3]; exact h3))
      fun t'' ⟨b, g, sm, r⟩ sy'' => ⟨⟨b, fun q hq => (g q hq).trans (o.gpr q (not_r12 hq)),
        (Same.of_mem o.mem _).trans sm, r⟩, sy''.trans (sy'.trans sy)⟩

/-- `update` through the table. -/
theorem updM_ok (hH : HashOK H) {t : State} (h : Base S vf s t) (sy : t.syms = s.syms) {dat : Addr} {len : Nat}
    (h3 : t.gpr .r3 = off (S s) oSt) (h5 : t.gpr .r5 = dat) (h6 : (t.gpr .r6).toNat = len)
    (h7 : t.gpr .r7 = off (S s) oW) (hdc : Covers [⟨dat, len⟩] (t.rd ++ t.wr))
    (hd₁ : Region.Disjoint ⟨dat, len⟩ ⟨off (S s) oSt, H.S⟩) (hd₂ : Region.Disjoint ⟨dat, len⟩ ⟨off (S s) oW, H.W⟩)
    (hd₃ : (cR s).Disjoint ⟨dat, len⟩) :
    WP isa (tcall j 1 f.upd) t fun t' => (Base S vf s t' ∧ (∀ r ∈ preserved, t'.gpr r = t.gpr r) ∧
      Same (S s) t t' [(oSt, H.S), (oW, H.W)] ∧
      ∀ m, hH.SH.Repr t.mem (off (S s) oSt) m → t.gpr .r4 = BitVec.ofNat 64 m.length →
        hH.SH.Repr t'.mem (off (S s) oSt) (m ++ Spec.Sha256.bytesAt t.mem dat len)) ∧ t'.syms = s.syms :=
  tcallM_ok T h sy (k := 1) (by decide) T.ok.u (by rw [Nat.mul_one]; exact T.mem.2.1)
    fun t' o sy' => WP.mono_syms (upd_ok P hH (h.only P o) (by rw [o.get .r3]; exact h3) (by rw [o.get .r5]; exact h5)
      (by rw [o.get .r6]; exact h6) (by rw [o.get .r7]; exact h7) (by rw [o.rd, o.wr]; exact hdc) hd₁ hd₂ hd₃)
      fun t'' ⟨b, g, sm, r⟩ sy'' => ⟨⟨b, fun q hq => (g q hq).trans (o.gpr q (not_r12 hq)),
        (Same.of_mem o.mem _).trans sm, fun m hm h4 => by
          have := r m (by rw [o.mem]; exact hm) (by rw [o.get .r4]; exact h4)
          rwa [o.mem] at this⟩, sy''.trans (sy'.trans sy)⟩

/-- `finalize` through the table. -/
theorem finM_ok (hH : HashOK H) {t : State} (h : Base S vf s t) (sy : t.syms = s.syms)
    (h3 : t.gpr .r3 = off (S s) oSt) (h5 : t.gpr .r5 = off (S s) oDig) (h6 : t.gpr .r6 = off (S s) oW) :
    WP isa (tcall j 2 f.fin) t fun t' => (Base S vf s t' ∧ (∀ r ∈ preserved, t'.gpr r = t.gpr r) ∧
      Same (S s) t t' [(oSt, H.S), (oDig, H.FD), (oW, H.W)] ∧
      ∀ m, hH.SH.Repr t.mem (off (S s) oSt) m → m.length < 2 ^ 64 → t.gpr .r4 = BitVec.ofNat 64 m.length →
        Spec.Sha256.bytesAt t'.mem (off (S s) oDig) H.FD = hH.fh m) ∧ t'.syms = s.syms :=
  tcallM_ok T h sy (k := 2) (by decide) T.ok.fz (by rw [show 8 * 2 = 16 from rfl]; exact T.mem.2.2)
    fun t' o sy' => WP.mono_syms (fin_ok P hH (h.only P o) (by rw [o.get .r3]; exact h3) (by rw [o.get .r5]; exact h5)
      (by rw [o.get .r6]; exact h6))
      fun t'' ⟨b, g, sm, r⟩ sy'' => ⟨⟨b, fun q hq => (g q hq).trans (o.gpr q (not_r12 hq)),
        (Same.of_mem o.mem _).trans sm, fun m hm hl h4 =>
          r m (by rw [o.mem]; exact hm) hl (by rw [o.get .r4]; exact h4)⟩, sy''.trans (sy'.trans sy)⟩

end

end VG.Proof.RsaPss.PPC64LE
