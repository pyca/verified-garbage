module

public import VerifiedGarbage.Proof.RsaOaep.RISCV64.MgfT
public import VerifiedGarbage.Proof.RsaPss.RISCV64.MdL
public import VerifiedGarbage.Impl.RsaPss.RISCV64
import VerifiedGarbage.Proof.Framework.ICall
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RISCV64.Syms
import VerifiedGarbage.Proof.Framework.RISCV64.Call

/-!
# RSASSA-PSS on RISC-V: the calls through the table of `MdHash`

Untrusted: everything here is checked by Lean. As RSAES-OAEP's calls through
a table of `Hash` (`Proof/RsaOaep/RISCV64/MgfT.lean`), for a table of
`MdHash` (`Spec/MdHashTable.lean`) that is our stack argument `j`, naming
the hash function `H` (`TabM`: what the table holds on entry, where nothing
we write reaches it, and that an indirect call of each of its first five
functions reaches `H`'s, its compression function and its digest of a hash
value `dN`): its words, read through the stack argument (`wp_twordM`); each
call through it (`tcallM_ok`) as `H`'s `init`, `update` and `finalize`
(`initM_ok`, `updM_ok`, `finM_ok`), its compression function of blocks in our
part of the working space (`compM_ok`), and its digest of the hash value at
`oSt` to `oDig` (`digM_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.RISCV64

open VG VG.RISCV64 VG.Impl.RsaPss.RISCV64 VG.WriteBytes
open VG.Impl.RsaOaep.RISCV64 (frameBytes oSt oDig oRsa tword tcall)
open VG.Impl.Hmac.Stream.RISCV64 (Hash)
open VG.Proof.Hmac.Stream.RISCV64 (HashOK)
open VG.Proof.RsaOaep.RISCV64 (Base Fits SC kR cR off Same init_ok upd_ok fin_ok same_of_frame frame208 sc_in
  sc_cov sdis not_t1 hfits offs)
open VG.Proof.RsaPkcs1Sig.RISCV64 (Only wp_ld wp_addSp wp_nil)
open VG.Proof.MdHashTable.RISCV64 (digestK)
open VG.Impl.MdHashTable.RISCV64 (digest)

/-! ## The table -/

/-- At `p` in `m`, the addresses `sy` gives `H`'s `init`, `update` and
`finalize`, its compression function `cN` and the digest `dN`. -/
def TabMemM (H : Hash) (cN dN : String) (sy : String → Addr) (p : Addr) (m : Mem) : Prop :=
  m.readW p 64 = sy H.initN ∧ m.readW (p + BitVec.ofNat 64 8) 64 = sy H.updN ∧
    m.readW (p + BitVec.ofNat 64 16) 64 = sy H.finN ∧ m.readW (p + BitVec.ofNat 64 24) 64 = sy cN ∧
    m.readW (p + BitVec.ofNat 64 32) 64 = sy dN

/-- An indirect call of `f`'s functions, at the addresses `sy` gives, to the
address of one of `H`'s functions, its compression function `cN` (of code
`cC`) or its digest `dN` (of code `dC`) reaches it. -/
structure TabOKM (H : Hash) (cN : String) (cC : Prog isa) (dN : String) (dC : Prog isa) (f : MdFns)
    (sy : String → Addr) : Prop where
  i : f.init.find? (fun q => sy q.1 == sy H.initN) = some (H.initN, H.initC)
  u : f.upd.find? (fun q => sy q.1 == sy H.updN) = some (H.updN, H.updC)
  fi : f.fin.find? (fun q => sy q.1 == sy H.finN) = some (H.finN, H.finC)
  c : f.comp.find? (fun q => sy q.1 == sy cN) = some (cN, cC)
  d : f.dig.find? (fun q => sy q.1 == sy dN) = some (dN, dC)

/-- The table of `MdHash` naming `H` (with `M`'s compression function and
the digest `dN` of `M`'s) at `p` that is our stack argument `j`, as on entry
`s`: the argument and the table's first five words readable, aligned, and
apart from what we write; the table holding the functions' addresses (an
indirect call reaching them). -/
structure TabM {H : Hash} {hH : HashOK H} (M : MdL H hH) (dN : String) (f : MdFns) (j : Nat)
    (S : State → Addr) (s : State) (p : Addr) : Prop where
  jo : frameBytes + 8 * j < 2048
  arg : s.mem.readW (stackArgAddr s j) 64 = p
  argA : (stackArgAddr s j).toNat % 8 = 0
  argR : InRegions s.rd (stackArgAddr s j) 8
  argK : Region.Disjoint ⟨stackArgAddr s j, 8⟩ (kR s)
  argS : Region.Disjoint ⟨stackArgAddr s j, 8⟩ (SC S s)
  pA : p.toNat % 8 = 0
  pw : p.toNat + 40 ≤ 2 ^ 64
  tR : ∀ k < 5, InRegions s.rd (p + BitVec.ofNat 64 (8 * k)) 8
  tK : ∀ k < 5, Region.Disjoint ⟨p + BitVec.ofNat 64 (8 * k), 8⟩ (kR s)
  tS : ∀ k < 5, Region.Disjoint ⟨p + BitVec.ofNat 64 (8 * k), 8⟩ (SC S s)
  mem : TabMemM H M.compN dN s.syms p s.mem
  ok : TabOKM H M.compN M.compC dN (digest M.out) f s.syms

/-- `TabM` of a state with `s`'s stack pointer, regions, statics' addresses
and working space, and memory as `s`'s apart from regions disjoint from the
stack argument and the table. -/
theorem TabM.transfer {H : Hash} {hH : HashOK H} {M : MdL H hH} {dN : String} {f : MdFns} {j : Nat}
    {S S' : State → Addr} {s s' : State} {p : Addr} (T : TabM M dN f j S s p) (hsp : s'.sp = s.sp)
    (hrd : s'.rd = s.rd) (hsy : s'.syms = s.syms) (hS : SC S' s' = SC S s) {rs : List Region}
    (hm : Frame rs s.mem s'.mem) (ha : ∀ r ∈ rs, Region.Disjoint ⟨stackArgAddr s j, 8⟩ r)
    (ht : ∀ k < 5, ∀ r ∈ rs, Region.Disjoint ⟨p + BitVec.ofNat 64 (8 * k), 8⟩ r) : TabM M dN f j S' s' p := by
  have eA : stackArgAddr s' j = stackArgAddr s j := by simp only [stackArgAddr, hsp]
  have eK : kR s' = kR s := by simp only [kR, hsp]
  have rd : ∀ k < 5, s'.mem.readW (p + BitVec.ofNat 64 (8 * k)) 64 = s.mem.readW (p + BitVec.ofNat 64 (8 * k)) 64 :=
    fun k hk => hm.readW (w := 64) (Region.contains_self _ _) (ht k hk) (by decide)
  obtain ⟨m0, m1, m2, m3, m4⟩ := T.mem
  have r0 := rd 0 (by decide)
  rw [show p + BitVec.ofNat 64 (8 * 0) = p by simp] at r0
  refine ⟨T.jo, ?_, by rw [eA]; exact T.argA, by rw [hrd, eA]; exact T.argR, by rw [eA, eK]; exact T.argK,
    by rw [eA, hS]; exact T.argS, T.pA, T.pw, fun k hk => by rw [hrd]; exact T.tR k hk,
    fun k hk => by rw [eK]; exact T.tK k hk, fun k hk => by rw [hS]; exact T.tS k hk, ⟨?_, ?_, ?_, ?_, ?_⟩,
    by rw [hsy]; exact T.ok⟩
  · rw [eA, hm.readW (w := 64) (Region.contains_self _ _) ha (by decide)]; exact T.arg
  · rw [hsy, r0]; exact m0
  · rw [hsy, rd 1 (by decide)]; exact m1
  · rw [hsy, rd 2 (by decide)]; exact m2
  · rw [hsy, rd 3 (by decide)]; exact m3
  · rw [hsy, rd 4 (by decide)]; exact m4

section
variable {H : Hash} {hH : HashOK H} {M : MdL H hH} {dN : String} {f : MdFns} {j : Nat} {S : State → Addr}
  {vf : State → Reg → BitVec 64} {s : State} {p : Addr} (T : TabM M dN f j S s p)
include T

/-- A word of the table is aligned. -/
theorem TabM.wA {k : Nat} (hk : k < 5) : (p + BitVec.ofNat 64 (8 * k)).toNat % 8 = 0 := by
  have h₁ := T.pA
  have h₂ := T.pw
  have e : (p + BitVec.ofNat 64 (8 * k)).toNat = p.toNat + 8 * k := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  rw [e]; omega

/-- The table's word `k` into `d`, through our stack argument `j`. -/
theorem wp_twordM {t : State} (h : Base S vf s t) {k : Nat} (hk : k < 5) {d : Reg} {is : List Instr}
    {Q : State → Prop}
    (kk : ∀ t', Only [d] t t' → t'.gpr d = s.mem.readW (p + BitVec.ofNat 64 (8 * k)) 64 → WP isa (.block is) t' Q) :
    WP isa (.block (tword d j k ++ is)) t Q := by
  simp only [tword, List.cons_append, List.nil_append]
  refine wp_addSp (h := T.jo) fun u₁ o₁ e₁ => wp_ld (a := stackArgAddr s j)
    (by rw [e₁, h.sp, ← Proof.RsaOaep.RISCV64.stackArgAddr_fb]; simp) T.argA
    (by rw [o₁.rd, h.rd]; exact let ⟨R, hR, hc⟩ := T.argR; ⟨R, List.mem_append_left _ hR, hc⟩)
    (fun u₂ o₂ e₂ => wp_ld (a := p + BitVec.ofNat 64 (8 * k))
      (by rw [e₂, o₁.mem, h.readW_apart T.argK T.argS, T.arg])
      (T.wA hk) (by rw [o₂.rd, o₁.rd, h.rd]; exact let ⟨R, hR, hc⟩ := T.tR k hk; ⟨R, List.mem_append_left _ hR, hc⟩)
      (fun u₃ o₃ e₃ => kk u₃ ((o₁.trans (o₂.trans o₃)).mono fun r hr => by
        simp only [List.mem_append, List.mem_singleton, or_self] at hr ⊢; exact hr) (by
        rw [e₃, o₂.mem, o₁.mem, h.readW_apart (T.tK k hk) (T.tS k hk)])) (by omega))

/-- The call of the table's function `k`, among `ts`, which reaches `n`, as
the call of `n` from the state the load of its address leaves. -/
theorem tcallM_ok {t : State} (h : Base S vf s t) (sy : t.syms = s.syms) {k : Nat} (hk : k < 5)
    {ts : List (String × Prog isa)} {n : String} {c : Prog isa}
    (hf : ts.find? (fun q => s.syms q.1 == s.syms n) = some (n, c))
    (hw : s.mem.readW (p + BitVec.ofNat 64 (8 * k)) 64 = s.syms n) {Q : State → Prop}
    (kk : ∀ t', Only [.t1] t t' → t'.syms = t.syms → WP isa (.call n c) t' Q) : WP isa (tcall j k ts) t Q := by
  show WP isa (.seq (.block (tword .t1 j k ++ [])) (Code.icalls (.jalr .t1) ts)) t Q
  refine WP.seq (WP.of_syms (wp_twordM T h hk fun t' o e => wp_nil fun sy' => ?_))
  refine WP.icalls_of_call (a := t'.gpr .t1) rfl ?_ (kk t' o sy')
  show ts.find? (fun q => t'.syms q.1 == t'.gpr .t1) = _
  rw [e, hw, sy', sy]; exact hf

section
variable (P : Fits S s)
include P

/-- `init` through the table. -/
theorem initM_ok (hF : H.F ≤ 208) {t : State} (h : Base S vf s t) (sy : t.syms = s.syms)
    (h0 : t.gpr .a0 = off (S s) oSt) :
    WP isa (tcall j 0 f.init) t fun t' => (Base S vf s t' ∧ (∀ r ∈ preserved, t'.gpr r = t.gpr r) ∧
      Same (S s) t t' [(oSt, H.S)] ∧ hH.SH.Repr t'.mem (off (S s) oSt) []) ∧ t'.syms = s.syms :=
  tcallM_ok T h sy (k := 0) (by decide) T.ok.i (by rw [Nat.mul_zero, BitVec.add_zero]; exact T.mem.1)
    fun t' o sy' => WP.mono_syms (init_ok P hH hF (h.only P o) (by rw [o.get .a0]; exact h0))
      fun t'' ⟨b, g, sm, r⟩ sy'' => ⟨⟨b, fun q hq => (g q hq).trans (o.gpr q (not_t1 hq)),
        (Same.of_mem o.mem _).trans sm, r⟩, sy''.trans (sy'.trans sy)⟩

/-- `update` through the table. -/
theorem updM_ok (hF : H.F ≤ 208) {t : State} (h : Base S vf s t) (sy : t.syms = s.syms)
    {dat : Addr} {len : Nat} (h0 : t.gpr .a0 = off (S s) oSt) (h2 : t.gpr .a2 = dat) (h3 : (t.gpr .a3).toNat = len)
    (hdc : Covers [⟨dat, len⟩] (t.rd ++ t.wr))
    (hd₁ : Region.Disjoint ⟨dat, len⟩ ⟨off (S s) oSt, H.S⟩) (hd₃ : (cR s).Disjoint ⟨dat, len⟩) :
    WP isa (tcall j 1 f.upd) t fun t' => (Base S vf s t' ∧ (∀ r ∈ preserved, t'.gpr r = t.gpr r) ∧
      Same (S s) t t' [(oSt, H.S)] ∧
      ∀ m, hH.SH.Repr t.mem (off (S s) oSt) m → t.gpr .a1 = BitVec.ofNat 64 m.length →
        hH.SH.Repr t'.mem (off (S s) oSt) (m ++ Spec.Sha256.bytesAt t.mem dat len)) ∧ t'.syms = s.syms :=
  tcallM_ok T h sy (k := 1) (by decide) T.ok.u (by rw [Nat.mul_one]; exact T.mem.2.1)
    fun t' o sy' => WP.mono_syms (upd_ok P hH hF (h.only P o) (by rw [o.get .a0]; exact h0)
      (by rw [o.get .a2]; exact h2) (by rw [o.get .a3]; exact h3) (by rw [o.rd, o.wr]; exact hdc) hd₁ hd₃)
      fun t'' ⟨b, g, sm, r⟩ sy'' => ⟨⟨b, fun q hq => (g q hq).trans (o.gpr q (not_t1 hq)),
        (Same.of_mem o.mem _).trans sm, fun m hm h1 => by
          have := r m (by rw [o.mem]; exact hm) (by rw [o.get .a1]; exact h1)
          rwa [o.mem] at this⟩, sy''.trans (sy'.trans sy)⟩

/-- `finalize` through the table. -/
theorem finM_ok (hF : H.F ≤ 208) {t : State} (h : Base S vf s t) (sy : t.syms = s.syms)
    (h0 : t.gpr .a0 = off (S s) oSt) (h2 : t.gpr .a2 = off (S s) oDig) :
    WP isa (tcall j 2 f.fin) t fun t' => (Base S vf s t' ∧ (∀ r ∈ preserved, t'.gpr r = t.gpr r) ∧
      Same (S s) t t' [(oSt, H.S), (oDig, H.D)] ∧
      ∀ m, hH.SH.Repr t.mem (off (S s) oSt) m → m.length < 2 ^ 64 → t.gpr .a1 = BitVec.ofNat 64 m.length →
        Spec.Sha256.bytesAt t'.mem (off (S s) oDig) H.D = hH.SH.H.hash m) ∧ t'.syms = s.syms :=
  tcallM_ok T h sy (k := 2) (by decide) T.ok.fi (by rw [show 8 * 2 = 16 from rfl]; exact T.mem.2.2.1)
    fun t' o sy' => WP.mono_syms (fin_ok P hH hF (h.only P o) (by rw [o.get .a0]; exact h0)
      (by rw [o.get .a2]; exact h2))
      fun t'' ⟨b, g, sm, r⟩ sy'' => ⟨⟨b, fun q hq => (g q hq).trans (o.gpr q (not_t1 hq)),
        (Same.of_mem o.mem _).trans sm, fun m hm hl h1 =>
          r m (by rw [o.mem]; exact hm) hl (by rw [o.get .a1]; exact h1)⟩, sy''.trans (sy'.trans sy)⟩

/-- The compression function through the table, of the `n` blocks at
`S + o` into the hash value at `S + oSt`, with the working space at
`S + oCs`. -/
theorem compM_ok (hal : (S s).toNat % 8 = 0) {t : State} (h : Base S vf s t) (sy : t.syms = s.syms)
    {o n : Nat} (h0 : t.gpr .a0 = off (S s) oSt) (h1 : t.gpr .a1 = off (S s) o)
    (h2 : t.gpr .a2 = BitVec.ofNat 64 n) (h3 : t.gpr .a3 = off (S s) oCs) (ho : oCs + 144 ≤ o)
    (hon : o + H.B * n ≤ oRsa) :
    WP isa (tcall j 3 f.comp) t fun t' => (Base S vf s t' ∧ (∀ r ∈ preserved, t'.gpr r = t.gpr r) ∧
      Same (S s) t t' [(oSt, H.N), (oCs, M.cs)] ∧
      M.md.stateAt t'.mem (off (S s) oSt) =
        M.md.compressBlocks (M.md.stateAt t.mem (off (S s) oSt)) t.mem (off (S s) o) n) ∧ t'.syms = s.syms := by
  have hN := hH.hN
  have hcs := M.hcs
  have hY : oCs = 1664 := rfl
  obtain ⟨_, hSt, _, _, hRs⟩ := offs
  have hn : n < 2 ^ 64 := by
    have : n ≤ H.B * n := Nat.le_mul_of_pos_left n (Nat.two_pow_pos _)
    unfold oRsa at hon; omega
  refine tcallM_ok T h sy (k := 3) (by decide) T.ok.c (by rw [show 8 * 3 = 24 from rfl]; exact T.mem.2.2.2.1)
    fun t' oo sy' => WP.mono_syms ?_ fun t'' q sy'' => ⟨q, sy''.trans (sy'.trans sy)⟩
  have g0 : t'.gpr .a0 = off (S s) oSt := by rw [oo.get .a0]; exact h0
  have g1 : t'.gpr .a1 = off (S s) o := by rw [oo.get .a1]; exact h1
  have g2 : t'.gpr .a2 = BitVec.ofNat 64 n := by rw [oo.get .a2]; exact h2
  have g3 : t'.gpr .a3 = off (S s) oCs := by rw [oo.get .a3]; exact h3
  have b' := h.only P oo
  have c0 : t'.callEntry.gpr .a0 = off (S s) oSt := (State.callEntry_gpr _ (by decide)).trans g0
  have c1 : t'.callEntry.gpr .a1 = off (S s) o := (State.callEntry_gpr _ (by decide)).trans g1
  have c2 : t'.callEntry.gpr .a2 = BitVec.ofNat 64 n := (State.callEntry_gpr _ (by decide)).trans g2
  have c3 : t'.callEntry.gpr .a3 = off (S s) oCs := (State.callEntry_gpr _ (by decide)).trans g3
  have e2 : (BitVec.ofNat 64 n).toNat = n := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  have hwc0 : Covers [⟨off (S s) oSt, H.N⟩, ⟨off (S s) oCs, M.cs⟩] (Proof.RsaOaep.RISCV64.fr s :: s.wr) :=
    Covers.pair (sc_cov P (by omega)) (sc_cov P (by omega))
  have hwc : Covers [⟨off (S s) oSt, H.N⟩, ⟨off (S s) oCs, M.cs⟩] t'.wr := by rw [b'.wr]; exact hwc0
  refine WP.call (k := compK M.md M.cs) M.comp (rd := [⟨off (S s) o, H.B * n⟩])
    (wr := [⟨off (S s) oSt, H.N⟩, ⟨off (S s) oCs, M.cs⟩]) ?_ ?_ hwc ?_ M.compNF
  · simp only [compK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, c0, c1, c2, c3, e2]
    refine ⟨trivial, trivial, sdis (.inl (by omega)) (by omega) (by omega), sdis (.inr (by omega)) hon (by omega),
      sdis (.inr (by omega)) hon (by omega), ?_⟩
    have e : (off (S s) oCs).toNat = (S s).toNat + oCs := by
      have := P.wS
      simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    show (off (S s) oCs).toNat % 8 = 0
    rw [e]; omega
  · rw [b'.rd, b'.wr]
    exact Covers.append_left (Covers.right (sc_cov P hon)) (Covers.right hwc0)
  · intro s' hrd hwr hsp hf hcs' _ hpost
    simp only [compK, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, c0, c1, c2, e2] at hpost
    have hf' : Frame ([⟨off (S s) oSt, H.N⟩, ⟨off (S s) oCs, M.cs⟩] ++ [below t'.sp 208]) t'.mem s'.mem :=
      hf.mono fun r hr => List.mem_append_left _ hr
    refine ⟨b'.call P (R := [⟨off (S s) oSt, H.N⟩, ⟨off (S s) oCs, M.cs⟩]) (fun r hr' => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
        rcases hr' with rfl | rfl
        · exact sc_in (by omega)
        · exact sc_in (by omega)) hrd hwr hsp hf' hcs',
      fun q hq => (hcs' q hq).trans (oo.gpr q (not_t1 hq)),
      (Same.of_mem oo.mem _).trans (same_of_frame P b'.sp (rgs := [(oSt, H.N), (oCs, M.cs)]) (by simp; omega) hf'),
      by rw [← oo.mem]; exact hpost⟩

/-- The digest through the table, of the hash value at `S + oSt` to
`S + oDig`. -/
theorem digM_ok {t : State} (h : Base S vf s t) (sy : t.syms = s.syms)
    (h0 : t.gpr .a0 = off (S s) oSt) (h1 : t.gpr .a1 = off (S s) oDig) :
    WP isa (tcall j 4 f.dig) t fun t' => (Base S vf s t' ∧ (∀ r ∈ preserved, t'.gpr r = t.gpr r) ∧
      Same (S s) t t' [(oDig, H.N)] ∧
      t'.mem = writeBytes t.mem (off (S s) oDig) (M.md.digest (M.md.stateAt t.mem (off (S s) oSt)))) ∧
      t'.syms = s.syms := by
  have hN := hH.hN
  obtain ⟨_, hSt, hDg, hCt, hRs⟩ := offs
  refine tcallM_ok T h sy (k := 4) (by decide) T.ok.d (by rw [show 8 * 4 = 32 from rfl]; exact T.mem.2.2.2.2)
    fun t' oo sy' => WP.mono_syms ?_ fun t'' q sy'' => ⟨q, sy''.trans (sy'.trans sy)⟩
  have g0 : t'.gpr .a0 = off (S s) oSt := by rw [oo.get .a0]; exact h0
  have g1 : t'.gpr .a1 = off (S s) oDig := by rw [oo.get .a1]; exact h1
  have b' := h.only P oo
  have c0 : t'.callEntry.gpr .a0 = off (S s) oSt := (State.callEntry_gpr _ (by decide)).trans g0
  have c1 : t'.callEntry.gpr .a1 = off (S s) oDig := (State.callEntry_gpr _ (by decide)).trans g1
  have hwc0 : Covers [⟨off (S s) oDig, H.N⟩] (Proof.RsaOaep.RISCV64.fr s :: s.wr) := sc_cov P (by omega)
  have hwc : Covers [⟨off (S s) oDig, H.N⟩] t'.wr := by rw [b'.wr]; exact hwc0
  refine WP.call (k := digestK M.md) (MdHashTable.RISCV64.digest_ok M.outOk) (rd := [⟨off (S s) oSt, H.N⟩])
    (wr := [⟨off (S s) oDig, H.N⟩]) ?_ ?_ hwc ?_ rfl
  · simp only [digestK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, c0, c1]
    exact ⟨trivial, trivial, sdis (.inl (by omega)) (by omega) (by omega)⟩
  · rw [b'.rd, b'.wr]
    exact Covers.append_left (Covers.right (sc_cov P (by omega))) (Covers.right hwc0)
  · intro s' hrd hwr hsp hf hcs' _ hpost
    simp only [digestK, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, c0, c1] at hpost
    have hf' : Frame ([⟨off (S s) oDig, H.N⟩] ++ [below t'.sp 208]) t'.mem s'.mem :=
      hf.mono fun r hr => List.mem_append_left _ hr
    refine ⟨b'.call P (R := [⟨off (S s) oDig, H.N⟩]) (fun r hr' => by
        rw [List.mem_singleton.mp hr']; exact sc_in (by omega)) hrd hwr hsp hf' hcs',
      fun q hq => (hcs' q hq).trans (oo.gpr q (not_t1 hq)),
      (Same.of_mem oo.mem _).trans (same_of_frame P b'.sp (rgs := [(oDig, H.N)]) (by simp; omega) hf'),
      by rw [hpost, oo.mem]⟩

end

end

end VG.Proof.RsaPss.RISCV64
