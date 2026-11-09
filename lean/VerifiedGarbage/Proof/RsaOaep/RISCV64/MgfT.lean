module

public import VerifiedGarbage.Proof.RsaOaep.RISCV64.Mgf
public import VerifiedGarbage.Proof.Framework.ICall
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.RISCV64.Syms

/-!
# RSAES-OAEP on RISC-V: MGF1 with the hash function of a table

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaOaep/PPC64LE/MgfStepsT.lean`, `MgfT.lean`), MGF1's round
(`Proof/RsaOaep/RISCV64/Mgf.lean`) with the hash function `G` of the table
that is our stack argument `j` (`TabS`: what the table holds on entry,
where nothing we write reaches it): its words, read through the stack
argument (`wp_tword`); `hLen`, its word 4 (`xorHeadT_ok`, `nextCtrT_ok`);
each call through it (`tcallT_ok`) as `G`'s (`initT_ok`, `updT_ok`,
`finT_ok`), the addresses of the statics being those of the entry;
`roundT_ok` and `mgfXorT_ok`, `dst ⊕= MGF1(src, dstLen)` in `EM`'s place.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.RISCV64

open VG VG.RISCV64 VG.Impl.RsaOaep.RISCV64 VG.WriteBytes
open VG.Impl.Hmac.Stream.RISCV64 (Hash)
open VG.Proof.Hmac.Stream.RISCV64 (HashOK)
open VG.Proof.RsaPkcs1Sig.RISCV64 (Only Kept MemTo wp_li wp_addi wp_subi wp_add wp_sub wp_and wp_xor wp_mov wp_srl
  wp_sb wp_lbu wp_ld wp_addSp wp_nil eval_nonzero)
open VG.Proof.RsaPkcs1Sig (bytesAt_length writeBytes_out)
open VG.Proof.RsaOaep (mixV srcB)
open VG.Proof.Mgf1 (ifp ifn)

/-! ## The table -/

/-- At `p` in `m`, the addresses `sy` gives `G`'s `init`, `update` and
`finalize`. -/
def TabMem (G : Hash) (sy : String → Addr) (p : Addr) (m : Mem) : Prop :=
  m.readW p 64 = sy G.initN ∧ m.readW (p + BitVec.ofNat 64 8) 64 = sy G.updN ∧
    m.readW (p + BitVec.ofNat 64 16) 64 = sy G.finN

/-- An indirect call of `f`'s functions, at the addresses `sy` gives, to the
address of one of `G`'s functions reaches it. -/
structure TabOK (G : Hash) (f : Fns) (sy : String → Addr) : Prop where
  i : f.init.find? (fun q => sy q.1 == sy G.initN) = some (G.initN, G.initC)
  u : f.upd.find? (fun q => sy q.1 == sy G.updN) = some (G.updN, G.updC)
  f : f.fin.find? (fun q => sy q.1 == sy G.finN) = some (G.finN, G.finC)

/-- The table of `G` at `p` that is our stack argument `j`, as on entry `s`:
the argument and the table readable, aligned, and apart from what we write
(`kR s`, our part of the working space); the table holding `G`'s
functions' addresses (an indirect call reaching them) and its digest
length. -/
structure TabS (G : Hash) (f : Fns) (j : Nat) (S : State → Addr) (s : State) (p : Addr) : Prop where
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
  mem : TabMem G s.syms p s.mem
  d : s.mem.readW (p + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 G.D
  ok : TabOK G f s.syms

/-- `TabS` of a state with `s`'s stack pointer, regions, statics' addresses
and working space, and memory as `s`'s apart from regions disjoint from the
stack argument and the table. -/
theorem TabS.transfer {G : Hash} {f : Fns} {j : Nat} {S S' : State → Addr} {s s' : State} {p : Addr}
    (T : TabS G f j S s p) (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd) (hsy : s'.syms = s.syms)
    (hS : SC S' s' = SC S s) {rs : List Region} (hm : Frame rs s.mem s'.mem)
    (ha : ∀ r ∈ rs, Region.Disjoint ⟨stackArgAddr s j, 8⟩ r)
    (ht : ∀ k < 5, ∀ r ∈ rs, Region.Disjoint ⟨p + BitVec.ofNat 64 (8 * k), 8⟩ r) : TabS G f j S' s' p := by
  have eA : stackArgAddr s' j = stackArgAddr s j := by simp only [stackArgAddr, hsp]
  have eK : kR s' = kR s := by simp only [kR, hsp]
  have rd : ∀ k < 5, s'.mem.readW (p + BitVec.ofNat 64 (8 * k)) 64 = s.mem.readW (p + BitVec.ofNat 64 (8 * k)) 64 :=
    fun k hk => hm.readW (w := 64) (Region.contains_self _ _) (ht k hk) (by decide)
  obtain ⟨m0, m1, m2⟩ := T.mem
  have r0 := rd 0 (by decide)
  rw [show p + BitVec.ofNat 64 (8 * 0) = p by simp] at r0
  refine ⟨T.jo, ?_, by rw [eA]; exact T.argA, by rw [hrd, eA]; exact T.argR, by rw [eA, eK]; exact T.argK,
    by rw [eA, hS]; exact T.argS, T.pA, T.pw, fun k hk => by rw [hrd]; exact T.tR k hk,
    fun k hk => by rw [eK]; exact T.tK k hk, fun k hk => by rw [hS]; exact T.tS k hk, ⟨?_, ?_, ?_⟩, ?_,
    by rw [hsy]; exact T.ok⟩
  · rw [eA, hm.readW (w := 64) (Region.contains_self _ _) ha (by decide)]; exact T.arg
  · rw [hsy, r0]; exact m0
  · rw [hsy, rd 1 (by decide)]; exact m1
  · rw [hsy, rd 2 (by decide)]; exact m2
  · rw [rd 4 (by decide)]; exact T.d

/-- A word of memory apart from what `Base` lets us write is as on entry. -/
theorem Base.readW_apart {S : State → Addr} {vf : State → Reg → BitVec 64} {s t : State} (h : Base S vf s t)
    {a : Addr} (hk : Region.Disjoint ⟨a, 8⟩ (kR s)) (hs : Region.Disjoint ⟨a, 8⟩ (SC S s)) :
    t.mem.readW a 64 = s.mem.readW a 64 :=
  (h.mem.readW (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hk
    · exact hs) (by decide))

/-- A word of the table is aligned. -/
theorem TabS.wA {G : Hash} {f : Fns} {j : Nat} {S : State → Addr} {s : State} {p : Addr}
    (T : TabS G f j S s p) {k : Nat} (hk : k < 5) : (p + BitVec.ofNat 64 (8 * k)).toNat % 8 = 0 := by
  have h₁ := T.pA
  have h₂ := T.pw
  have e : (p + BitVec.ofNat 64 (8 * k)).toNat = p.toNat + 8 * k := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  rw [e]; omega

/-- The table's word `k` into `d`, through our stack argument `j`. -/
theorem wp_tword {G : Hash} {f : Fns} {j : Nat} {S : State → Addr} {vf : State → Reg → BitVec 64} {s t : State}
    {p : Addr} (T : TabS G f j S s p) (h : Base S vf s t) {k : Nat} (hk : k < 5) {d : Reg}
    {is : List Instr} {Q : State → Prop}
    (kk : ∀ t', Only [d] t t' → t'.gpr d = s.mem.readW (p + BitVec.ofNat 64 (8 * k)) 64 → WP isa (.block is) t' Q) :
    WP isa (.block (tword d j k ++ is)) t Q := by
  simp only [tword, List.cons_append, List.nil_append]
  refine wp_addSp (h := T.jo) fun u₁ o₁ e₁ => wp_ld (a := stackArgAddr s j)
    (by rw [e₁, h.sp, ← stackArgAddr_fb]; simp) T.argA
    (by rw [o₁.rd, h.rd]; exact let ⟨R, hR, hc⟩ := T.argR; ⟨R, List.mem_append_left _ hR, hc⟩)
    (fun u₂ o₂ e₂ => wp_ld (a := p + BitVec.ofNat 64 (8 * k)) (by rw [e₂, o₁.mem, h.readW_apart T.argK T.argS, T.arg])
      (T.wA hk) (by rw [o₂.rd, o₁.rd, h.rd]; exact let ⟨R, hR, hc⟩ := T.tR k hk; ⟨R, List.mem_append_left _ hR, hc⟩)
      (fun u₃ o₃ e₃ => kk u₃ ((o₁.trans (o₂.trans o₃)).mono fun r hr => by
        simp only [List.mem_append, List.mem_singleton, or_self] at hr ⊢; exact hr) (by
        rw [e₃, o₂.mem, o₁.mem, h.readW_apart (T.tK k hk) (T.tS k hk)])) (by omega))

/-- How many bytes of the digest go into `dst`: `min(hLen, dstLen - done)`,
`hLen` the table's word 4. -/
theorem xorHeadT_ok {G : Hash} {f : Fns} {j : Nat} {S' : State → Addr} {vf : State → Reg → BitVec 64} {s₀ : State}
    {p : Addr} (T : TabS G f j S' s₀ p) {t : State} (hb : Base S' vf s₀ t) {S : Addr} {dst dstLen done : Nat}
    (hD : G.D < 2048) (h0 : t.gpr .s0 = S) (h8 : t.gpr .s8 = off S dst) (h9 : t.gpr .s9 = BitVec.ofNat 64 dstLen)
    (h11 : t.gpr .s11 = BitVec.ofNat 64 done) (hlt : done < dstLen) (hdl : dstLen < 2 ^ 63) :
    WP isa (.block (xorHeadT j)) t fun t' => Only [.a4, .a5, .a6, .t1, .t2, .t3, .t4] t t' ∧
      t'.gpr .a4 = off S oDig ∧ t'.gpr .a5 = off S (dst + done) ∧
      t'.gpr .a6 = BitVec.ofNat 64 (min G.D (dstLen - done)) := by
  simp only [xorHeadT]
  refine wp_tword T hb (k := 4) (by decide) fun u₀ o₀ e₀ => ?_
  rw [show 8 * 4 = 32 from rfl, T.d] at e₀
  refine wp_addi (imm := oDig) fun u₁ o₁ e₁ => wp_add fun u₂ o₂ e₂ => wp_sub fun u₃ o₃ e₃ =>
    wp_sub fun u₅ o₅ e₅ => wp_srl fun u₆ o₆ e₆ =>
    wp_li (imm := 0) (by decide) fun u₇ o₇ e₇ => wp_sub fun u₈ o₈ e₈ =>
    wp_and fun u₉ o₉ e₉ => wp_add fun u₁₀ o₁₀ e₁₀ => wp_nil ?_
  have k : Only [.a4, .a5, .a6, .t1, .t2, .t3, .t4] t u₁₀ :=
    (o₀.trans (o₁.trans (o₂.trans (o₃.trans (o₅.trans (o₆.trans (o₇.trans (o₈.trans (o₉.trans o₁₀))))))))).mono
  have r1 : u₃.gpr .t1 = BitVec.ofNat 64 (dstLen - done) := by
    rw [e₃, o₂.get .s9, o₂.get .s11, o₁.get .s9, o₁.get .s11, o₀.get .s9, o₀.get .s11, h9, h11,
      Offset.ofNat_sub_ofNat (by omega)]
  have r6 : u₃.gpr .a6 = BitVec.ofNat 64 G.D := by rw [o₃.get .a6, o₂.get .a6, o₁.get .a6, e₀]
  have r2 : u₅.gpr .t2 = BitVec.ofNat 64 (dstLen - done) - BitVec.ofNat 64 G.D := by
    rw [e₅, r1, r6]
  have hD := T.d
  refine ⟨k, ?_, ?_, ?_⟩
  · rw [o₁₀.get .a4, o₉.get .a4, o₈.get .a4, o₇.get .a4, o₆.get .a4, o₅.get .a4, o₃.get .a4,
      o₂.get .a4, e₁, o₀.get .s0, h0]
  · rw [o₁₀.get .a5, o₉.get .a5, o₈.get .a5, o₇.get .a5, o₆.get .a5, o₅.get .a5, o₃.get .a5, e₂,
      o₁.get .s8, o₁.get .s11, o₀.get .s8, o₀.get .s11, h8, h11, off_add]
  · rw [e₁₀, o₉.get .a6, o₈.get .a6, o₇.get .a6, o₆.get .a6, o₅.get .a6, r6, e₉, o₈.get .t2, o₇.get .t2,
      o₆.get .t2, r2, e₈, e₇, o₇.get .t3, e₆, r2]
    exact minSel (by omega) (by omega)

/-- `nextCtrT`: the next counter and `done`, and in `t1` whether `done` is
still below `dstLen`. -/
theorem nextCtrT_ok {G : Hash} {f : Fns} {j : Nat} {S' : State → Addr} {vf : State → Reg → BitVec 64} {s₀ : State}
    {p : Addr} (T : TabS G f j S' s₀ p) {t : State} (hb : Base S' vf s₀ t) {c done dstLen : Nat}
    (h10 : t.gpr .s10 = BitVec.ofNat 64 c) (h11 : t.gpr .s11 = BitVec.ofNat 64 done)
    (h9 : t.gpr .s9 = BitVec.ofNat 64 dstLen) (hd : done + G.D < 2 ^ 63) (hdl : dstLen < 2 ^ 63) :
    WP isa (.block (nextCtrT j)) t fun t' => Only [.s10, .s11, .t1] t t' ∧
      t'.gpr .s10 = BitVec.ofNat 64 (c + 1) ∧ t'.gpr .s11 = BitVec.ofNat 64 (done + G.D) ∧
      (t'.gpr .t1 != 0) = decide (done + G.D < dstLen) := by
  simp only [nextCtrT]
  refine wp_tword T hb (k := 4) (by decide) fun u₀ o₀ e₀ => ?_
  rw [show 8 * 4 = 32 from rfl, T.d] at e₀
  refine wp_addi (imm := 1) fun u₁ o₁ e₁ => wp_add fun u₂ o₂ e₂ => wp_sub fun u₃ o₃ e₃ =>
    wp_srl fun u₄ o₄ e₄ => wp_nil ⟨(o₀.trans (o₁.trans (o₂.trans (o₃.trans o₄)))).mono, ?_, ?_, ?_⟩
  · rw [o₄.get .s10, o₃.get .s10, o₂.get .s10, e₁, o₀.get .s10, h10, BitVec.ofNat_add]
  · rw [o₄.get .s11, o₃.get .s11, e₂, o₁.get .s11, o₁.get .t1, o₀.get .s11, h11, e₀, BitVec.ofNat_add]
  · rw [e₄, e₃, o₂.get .s9, e₂, o₁.get .s11, o₁.get .s9, o₁.get .t1, o₀.get .s11, o₀.get .s9, h11, h9, e₀,
      ← BitVec.ofNat_add]
    exact ne_zero_ltBit hd hdl

/-! ## The rounds -/

/-- After `c` rounds: `Base`, MGF1's registers, and the first
`min(c D, dstLen)` bytes of the mask `mk` XORed into `dst` in `EM`'s place,
whose view was `V`, and the entry's addresses of statics. -/
structure MgfIT (S : State → Addr) (vf : State → Reg → BitVec 64) (s : State) (V : Nat → Byte) (mk : List Byte)
    (src srcLen dst dstLen D c : Nat) (v : State) : Prop where
  base : Base S vf s v
  s6 : v.gpr .s6 = off (S s) src
  s7 : v.gpr .s7 = BitVec.ofNat 64 srcLen
  s8 : v.gpr .s8 = off (S s) dst
  s9 : v.gpr .s9 = BitVec.ofNat 64 dstLen
  s10 : v.gpr .s10 = BitVec.ofNat 64 c
  s11 : v.gpr .s11 = BitVec.ofNat 64 (c * D)
  em : ∀ o, Kp o → view v.mem (S s) o = mixV V mk dst (min (c * D) dstLen) o
  sy : v.syms = s.syms

section
variable {S : State → Addr} {vf : State → Reg → BitVec 64} {s : State} (P : Fits S s)
include P

omit P in
theorem not_t1 {r : Reg} (hr : r ∈ preserved) : r ∉ [.t1] := fun h' => by
  rw [List.mem_singleton] at h'; subst h'; exact absurd hr (by decide)

section TCall
variable {G : Hash} {f : Fns} {j : Nat} {p : Addr} (T : TabS G f j S s p)
include T

omit P in
/-- The call of the table's function `k`, among `ts`, which reaches `n`, as
the call of `n` from the state the load of its address leaves. -/
theorem tcallT_ok {t : State} (h : Base S vf s t) (sy : t.syms = s.syms) {k : Nat} (hk : k < 3)
    {ts : List (String × Prog isa)} {n : String} {c : Prog isa}
    (hf : ts.find? (fun q => s.syms q.1 == s.syms n) = some (n, c))
    (hw : s.mem.readW (p + BitVec.ofNat 64 (8 * k)) 64 = s.syms n) {Q : State → Prop}
    (kk : ∀ t', Only [.t1] t t' → t'.syms = t.syms → WP isa (.call n c) t' Q) : WP isa (tcall j k ts) t Q := by
  show WP isa (.seq (.block (tword .t1 j k ++ [])) (Code.icalls (.jalr .t1) ts)) t Q
  refine WP.seq (WP.of_syms (wp_tword T h (by omega) fun t' o e => wp_nil fun sy' => ?_))
  refine WP.icalls_of_call (a := t'.gpr .t1) rfl ?_ (kk t' o sy')
  show ts.find? (fun q => t'.syms q.1 == t'.gpr .t1) = _
  rw [e, hw, sy', sy]; exact hf

/-- `init` through the table. -/
theorem initT_ok (hG : HashOK G) (hF : G.F ≤ 208) {t : State} (h : Base S vf s t) (sy : t.syms = s.syms)
    (h0 : t.gpr .a0 = off (S s) oSt) :
    WP isa (tcall j 0 f.init) t fun t' => (Base S vf s t' ∧ (∀ r ∈ preserved, t'.gpr r = t.gpr r) ∧
      Same (S s) t t' [(oSt, G.S)] ∧ hG.SH.Repr t'.mem (off (S s) oSt) []) ∧ t'.syms = s.syms :=
  tcallT_ok T h sy (k := 0) (by decide) T.ok.i (by rw [Nat.mul_zero, BitVec.add_zero]; exact T.mem.1)
    fun t' o sy' => WP.mono_syms (init_ok P hG hF (h.only P o) (by rw [o.get .a0]; exact h0))
      fun t'' ⟨b, g, sm, r⟩ sy'' => ⟨⟨b, fun q hq => (g q hq).trans (o.gpr q (not_t1 hq)),
        (Same.of_mem o.mem _).trans sm, r⟩, sy''.trans (sy'.trans sy)⟩

/-- `update` through the table. -/
theorem updT_ok (hG : HashOK G) (hF : G.F ≤ 208) {t : State} (h : Base S vf s t) (sy : t.syms = s.syms)
    {dat : Addr} {len : Nat} (h0 : t.gpr .a0 = off (S s) oSt) (h2 : t.gpr .a2 = dat) (h3 : (t.gpr .a3).toNat = len)
    (hdc : Covers [⟨dat, len⟩] (t.rd ++ t.wr))
    (hd₁ : Region.Disjoint ⟨dat, len⟩ ⟨off (S s) oSt, G.S⟩) (hd₃ : (cR s).Disjoint ⟨dat, len⟩) :
    WP isa (tcall j 1 f.upd) t fun t' => (Base S vf s t' ∧ (∀ r ∈ preserved, t'.gpr r = t.gpr r) ∧
      Same (S s) t t' [(oSt, G.S)] ∧
      ∀ m, hG.SH.Repr t.mem (off (S s) oSt) m → t.gpr .a1 = BitVec.ofNat 64 m.length →
        hG.SH.Repr t'.mem (off (S s) oSt) (m ++ Spec.Sha256.bytesAt t.mem dat len)) ∧ t'.syms = s.syms :=
  tcallT_ok T h sy (k := 1) (by decide) T.ok.u (by rw [Nat.mul_one]; exact T.mem.2.1)
    fun t' o sy' => WP.mono_syms (upd_ok P hG hF (h.only P o) (by rw [o.get .a0]; exact h0)
      (by rw [o.get .a2]; exact h2) (by rw [o.get .a3]; exact h3) (by rw [o.rd, o.wr]; exact hdc) hd₁ hd₃)
      fun t'' ⟨b, g, sm, r⟩ sy'' => ⟨⟨b, fun q hq => (g q hq).trans (o.gpr q (not_t1 hq)),
        (Same.of_mem o.mem _).trans sm, fun m hm h1 => by
          have := r m (by rw [o.mem]; exact hm) (by rw [o.get .a1]; exact h1)
          rwa [o.mem] at this⟩, sy''.trans (sy'.trans sy)⟩

/-- `finalize` through the table. -/
theorem finT_ok (hG : HashOK G) (hF : G.F ≤ 208) {t : State} (h : Base S vf s t) (sy : t.syms = s.syms)
    (h0 : t.gpr .a0 = off (S s) oSt) (h2 : t.gpr .a2 = off (S s) oDig) :
    WP isa (tcall j 2 f.fin) t fun t' => (Base S vf s t' ∧ (∀ r ∈ preserved, t'.gpr r = t.gpr r) ∧
      Same (S s) t t' [(oSt, G.S), (oDig, G.D)] ∧
      ∀ m, hG.SH.Repr t.mem (off (S s) oSt) m → m.length < 2 ^ 64 → t.gpr .a1 = BitVec.ofNat 64 m.length →
        Spec.Sha256.bytesAt t'.mem (off (S s) oDig) G.D = hG.SH.H.hash m) ∧ t'.syms = s.syms :=
  tcallT_ok T h sy (k := 2) (by decide) T.ok.f (by rw [show 8 * 2 = 16 from rfl]; exact T.mem.2.2)
    fun t' o sy' => WP.mono_syms (fin_ok P hG hF (h.only P o) (by rw [o.get .a0]; exact h0)
      (by rw [o.get .a2]; exact h2))
      fun t'' ⟨b, g, sm, r⟩ sy'' => ⟨⟨b, fun q hq => (g q hq).trans (o.gpr q (not_t1 hq)),
        (Same.of_mem o.mem _).trans sm, fun m hm hl h1 =>
          r m (by rw [o.mem]; exact hm) hl (by rw [o.get .a1]; exact h1)⟩, sy''.trans (sy'.trans sy)⟩

end TCall

theorem roundT_ok {G : Hash} (hG : HashOK G) (hF : G.F ≤ 208) {f : Fns} {j : Nat} {p : Addr}
    (T : TabS G f j S s p) {Gs : Spec.Mgf1.Hash}
    (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = G.D) (hGv : Proof.Mgf1.Valid Gs) {V : Nat → Byte}
    {src srcLen dst dstLen c : Nat} (hf : MFit src srcLen dst dstLen) {v : State}
    (I : MgfIT S vf s V (Spec.Mgf1.mgf1 Gs (srcB V src srcLen) dstLen) src srcLen dst dstLen G.D c v)
    (hc : c * G.D < dstLen) :
    WP isa (roundT f j) v fun v' => (v'.gpr .t1 != 0) = decide ((c + 1) * G.D < dstLen) ∧
      MgfIT S vf s V (Spec.Mgf1.mgf1 Gs (srcB V src srcLen) dstLen) src srcLen dst dstLen G.D (c + 1) v' := by
  have F := hfits hG
  obtain ⟨_, hSt, hDg, hCt, hRs⟩ := offs
  have hD0 := hG.hD0
  have hD64 := hG.hD64
  have hfs := hf.fs
  have hfd := hf.fd
  have hsep := hf.sep
  have hcD : c ≤ c * G.D := Nat.le_mul_of_pos_right c hD0
  -- The registers MGF1 keeps.
  let mg : List Reg := [.s6, .s7, .s8, .s9, .s10, .s11]
  have pm : ∀ r ∈ mg, r ∈ preserved := by decide
  refine WP.of_syms ?_
  -- `init`.
  refine WP.seq (WP.of_syms (wp_addi (imm := oSt) fun t₁ o₁ e₁ => wp_nil fun sy₁ => ?_))
  have b₁ := I.base.only P o₁
  refine WP.seq (WP.mono (initT_ok P T hG hF b₁ (sy₁.trans I.sy) (by rw [e₁, I.base.s0]))
    fun t₂ ⟨⟨b₂, g₂, s₂, r₂⟩, sy₂⟩ => ?_)
  have m₂ : ∀ r ∈ mg, t₂.gpr r = v.gpr r := fun r hr => by
    rw [g₂ r (pm r hr), o₁.gpr r (by revert r; decide)]
  -- `update` with `src`.
  refine WP.seq (WP.of_syms (wp_addi (imm := oSt) fun t₃ o₃ e₃ => wp_li (imm := 0) (by decide) fun t₄ o₄ e₄ =>
    wp_mov fun t₅ o₅ e₅ => wp_mov fun t₆ o₆ e₆ => wp_nil fun sy₆ => ?_))
  have k₆ : Only [.a0, .a1, .a2, .a3] t₂ t₆ := (o₃.trans (o₄.trans (o₅.trans o₆))).mono
  have b₆ := b₂.only P k₆
  refine WP.seq (WP.mono (updT_ok P T hG hF b₆ (sy₆.trans sy₂) (dat := off (S s) src) (len := srcLen)
    (by rw [o₆.get .a0, o₅.get .a0, o₄.get .a0, e₃, b₂.s0])
    (by rw [o₆.get .a2, e₅, o₄.get .s6, o₃.get .s6, m₂ _ (by decide), I.s6])
    (by rw [e₆, o₅.get .s7, o₄.get .s7, o₃.get .s7, m₂ _ (by decide), I.s7, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega)])
    (Covers.right (by rw [b₆.wr]; exact sc_cov P (by omega))) (sdis (.inl (by omega)) (by omega) (by omega))
    (cR_dis P (by omega))) fun t₇ ⟨⟨b₇, g₇, s₇, r₇⟩, sy₇⟩ => ?_)
  have m₇ : ∀ r ∈ mg, t₇.gpr r = v.gpr r := fun r hr => by
    rw [g₇ r (pm r hr), k₆.gpr r (by revert r; decide), m₂ r hr]
  have hsrc : Spec.Rsa.bytesAt t₆.mem (off (S s) src) srcLen = srcB V src srcLen := by
    rw [bytesAt_view]
    refine List.map_congr_left fun i hi => ?_
    have hi := List.mem_range.mp hi
    rw [k₆.mem, s₂ _ (by omega) (by simp; omega), o₁.mem, I.em _ ⟨by omega, .inl (by omega)⟩, mixV, ifn (by omega)]
  have hR7 : hG.SH.Repr t₇.mem (off (S s) oSt) (srcB V src srcLen) := by
    have := r₇ [] (by rw [k₆.mem]; exact r₂) (by rw [o₆.get .a1, o₅.get .a1, e₄]; rfl)
    rw [List.nil_append] at this
    exact hsrc ▸ this
  -- The counter, and `update` with it.
  refine WP.seq (WP.mono_syms (ctr_ok P b₇ (c := c) (by rw [m₇ _ (by decide), I.s10]) (by omega))
    fun t₈ ⟨b₈, g₈, v₈, x0, x1, x2, x3⟩ sy₈ => ?_)
  have m₈ : ∀ r ∈ mg, t₈.gpr r = v.gpr r := fun r hr => by rw [g₈ r (pm r hr), m₇ r hr]
  have hR8 : hG.SH.Repr t₈.mem (off (S s) oSt) (srcB V src srcLen) :=
    hG.congr t₇.mem t₈.mem (off (S s) oSt) _ (fun i hi => by
      have e := v₈ (oSt + i) (by omega)
      simp only [view, ctrV] at e
      rw [ifn (by omega)] at e
      rw [off_add]; exact e) hR7
  refine WP.seq (WP.mono (updT_ok P T hG hF b₈ (sy₈.trans sy₇) (dat := off (S s) oCtr) (len := 4) x0 x2
    (by rw [x3]; rfl)
    (Covers.right (by rw [b₈.wr]; exact sc_cov P (by omega))) (sdis (.inr (by omega)) (by omega) (by omega))
    (cR_dis P (by omega))) fun t₉ ⟨⟨b₉, g₉, s₉, r₉⟩, sy₉⟩ => ?_)
  have m₉ : ∀ r ∈ mg, t₉.gpr r = v.gpr r := fun r hr => by rw [g₉ r (pm r hr), m₈ r hr]
  have hctr : Spec.Rsa.bytesAt t₈.mem (off (S s) oCtr) 4 = Spec.Rsa.i2osp c 4 := by
    rw [bytesAt_view]
    refine (List.map_congr_left fun i hi => ?_).trans ((RsaOaep.range_map_getD (n := 4)
      (xs := Spec.Rsa.i2osp c 4) (by rw [Proof.Mgf1.i2osp_length])).trans
      (List.take_of_length_le (by rw [Proof.Mgf1.i2osp_length])))
    have := List.mem_range.mp hi
    rw [v₈ _ (by omega), ctrV, ifp (by omega), Nat.add_sub_cancel_left]
  have hml : (srcB V src srcLen).length = srcLen := by simp [srcB]
  have hR9 : hG.SH.Repr t₉.mem (off (S s) oSt) (srcB V src srcLen ++ Spec.Rsa.i2osp c 4) := by
    have := r₉ _ hR8 (by rw [x1, m₇ _ (by decide), I.s7, hml])
    exact hctr ▸ this
  -- `finalize`.
  refine WP.seq (WP.of_syms (wp_addi (imm := oSt) fun t₁₀ o₁₀ e₁₀ => wp_addi (imm := 4) fun t₁₁ o₁₁ e₁₁ =>
    wp_addi (imm := oDig) fun t₁₂ o₁₂ e₁₂ => wp_nil fun sy₁₂ => ?_))
  have k₁₂ : Only [.a0, .a1, .a2] t₉ t₁₂ := (o₁₀.trans (o₁₁.trans o₁₂)).mono
  have b₁₂ := b₉.only P k₁₂
  have hl4 : (srcB V src srcLen ++ Spec.Rsa.i2osp c 4).length = srcLen + 4 := by
    rw [List.length_append, hml, Proof.Mgf1.i2osp_length]
  refine WP.seq (WP.mono (finT_ok P T hG hF b₁₂ (sy₁₂.trans sy₉) (by rw [o₁₂.get .a0, o₁₁.get .a0, e₁₀, b₉.s0])
    (by rw [e₁₂, o₁₁.get .s0, o₁₀.get .s0, b₉.s0])) fun t₁₃ ⟨⟨b₁₃, g₁₃, s₁₃, r₁₃⟩, _⟩ => ?_)
  have m₁₃ : ∀ r ∈ mg, t₁₃.gpr r = v.gpr r := fun r hr => by
    rw [g₁₃ r (pm r hr), k₁₂.gpr r (by revert r; decide), m₉ r hr]
  have hfh := r₁₃ _ (by rw [k₁₂.mem]; exact hR9) (by rw [hl4]; omega)
    (by rw [o₁₂.get .a1, e₁₁, o₁₀.get .s7, m₉ _ (by decide), I.s7, hl4, BitVec.ofNat_add])
  have hdig : ∀ j < G.D, view t₁₃.mem (S s) (oDig + j) =
      (Gs.hash (srcB V src srcLen ++ Spec.Rsa.i2osp c 4)).getD j 0 := fun j hj => by
    rw [hGh, ← hfh, view, ← off_add]
    simp only [Spec.Sha256.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]
    rfl
  -- Into `dst`.
  have hdc := Nat.min_le_left G.D (dstLen - c * G.D)
  have hn0 : 0 < min G.D (dstLen - c * G.D) := by omega
  refine WP.seq (WP.seq (WP.mono (xorHeadT_ok T b₁₃ (G := G) (S := S s) (dst := dst) (dstLen := dstLen)
    (done := c * G.D) (by omega) b₁₃.s0 (by rw [m₁₃ _ (by decide), I.s8]) (by rw [m₁₃ _ (by decide), I.s9])
    (by rw [m₁₃ _ (by decide), I.s11]) hc (by omega)) fun t₁₄ ⟨k₁₄, x4, x5, x6⟩ => ?_))
  have b₁₄ := b₁₃.only P k₁₄
  refine WP.mono (xorLoop_ok (p := off (S s) (dst + c * G.D)) (q := off (S s) oDig) hn0 (by omega) x4 x5 x6
    (fun j hj => by
      rw [off_add, k₁₄.rd, k₁₄.wr, b₁₃.wr, b₁₃.rd]; exact sc_inR P (by omega) _)
    (sc_w P (by rw [k₁₄.wr, b₁₃.wr]) (by omega))
    (fun j hj i hi => by
      rw [off_add, off_add]; exact Offset.add_ofNat_ne _ (by omega) (by omega) (by omega))
    (fun i hi j hj hij => by
      rw [off_add, off_add]; exact Offset.add_ofNat_ne _ (by omega) (by omega) (by omega)))
    fun t₁₅ ⟨k₁₅, x₁₅⟩ => ?_
  have b₁₅ : Base S vf s t₁₅ := b₁₄.wb P k₁₅ (by rw [xorAt_length]; omega) x₁₅
  have m₁₅ : ∀ r ∈ mg, t₁₅.gpr r = v.gpr r := fun r hr => by
    rw [k₁₅.gpr r (by revert r; decide), k₁₄.gpr r (by revert r; decide), m₁₃ r hr]
  -- The next counter.
  refine WP.mono (nextCtrT_ok T b₁₅ (G := G) (c := c) (done := c * G.D) (dstLen := dstLen)
    (by rw [m₁₅ _ (by decide), I.s10]) (by rw [m₁₅ _ (by decide), I.s11]) (by rw [m₁₅ _ (by decide), I.s9])
    (by omega) (by omega)) fun t₁₆ ⟨k₁₆, x10, x11, xt⟩ hsy => ?_
  have hs1 : (c + 1) * G.D = c * G.D + G.D := Nat.succ_mul _ _
  refine ⟨by rw [xt, hs1], b₁₅.only P k₁₆, by rw [k₁₆.get .s6, m₁₅ _ (by decide), I.s6],
    by rw [k₁₆.get .s7, m₁₅ _ (by decide), I.s7], by rw [k₁₆.get .s8, m₁₅ _ (by decide), I.s8],
    by rw [k₁₆.get .s9, m₁₅ _ (by decide), I.s9], x10, by rw [x11, hs1], fun o ⟨ho, ho'⟩ => ?_, hsy.trans I.sy⟩
  -- `EM`'s place.
  have hold : view t₁₃.mem (S s) o = view v.mem (S s) o := by
    have e₁₃ := s₁₃ o (by omega) (by simp; omega)
    have e₉ := s₉ o (by omega) (by simp; omega)
    have e₈ := v₈ o (by omega)
    have e₇ := s₇ o (by omega) (by simp; omega)
    have e₂ := s₂ o (by omega) (by simp; omega)
    simp only [ctrV] at e₈
    rw [ifn (by omega)] at e₈
    simp only [view] at *
    rw [e₁₃, k₁₂.mem, e₉, e₈, e₇, k₆.mem, e₂, o₁.mem]
  have hv : view t₁₆.mem (S s) o = if dst + c * G.D ≤ o ∧ o < dst + c * G.D + min G.D (dstLen - c * G.D) then
      view v.mem (S s) o ^^^ (Gs.hash (srcB V src srcLen ++ Spec.Rsa.i2osp c 4)).getD (o - (dst + c * G.D)) 0
      else view v.mem (S s) o := by
    rw [k₁₆.mem, x₁₅, k₁₄.mem, view_wb _ _ (by rw [xorAt_length]; omega) (by omega), xorAt_length]
    split
    · rename_i hx
      rw [xorAt_getD _ _ _ (by omega), off_add, off_add,
        show dst + c * G.D + (o - (dst + c * G.D)) = o by omega, ← hold]
      simp only [view]
      rw [← hdig _ (by omega)]
      simp only [view]
    · exact hold
  rw [hv]
  by_cases hx : dst + c * G.D ≤ o ∧ o < dst + c * G.D + min G.D (dstLen - c * G.D)
  · have hs2 : G.D * (c + 1) = c * G.D + G.D := by rw [Nat.mul_comm]; exact hs1
    have hs3 : G.D * c = c * G.D := Nat.mul_comm _ _
    have hq : (o - dst) / G.D = c := Nat.div_eq_of_lt_le (by omega) (by omega)
    have hr : (o - dst) % G.D = o - (dst + c * G.D) := by
      rw [Nat.mod_eq_sub_mul_div, hq, Nat.mul_comm]; omega
    rw [ifp hx, I.em o ⟨ho, ho'⟩, mixV, mixV, ifn (by omega), ifp (by rw [hs1]; omega),
      Proof.Mgf1.mgf1_getD hGv _ (show o - dst < dstLen by omega), hGl, hq, hr]
  · rw [ifn hx, I.em o ⟨ho, ho'⟩, mixV, mixV]
    by_cases hy : dst ≤ o ∧ o < dst + min (c * G.D) dstLen
    · rw [ifp hy, ifp (by rw [hs1]; omega)]
    · rw [ifn hy, ifn (by rw [hs1]; omega)]

/-- `dst ⊕= MGF1(src, dstLen)` in `EM`'s place, from `src`, `srcLen`, `dst`
and `dstLen` in `s6`–`s9`, with the hash function of the table that is our
stack argument `j`. -/
theorem mgfXorT_ok {G : Hash} (hG : HashOK G) (hF : G.F ≤ 208) {f : Fns} {j : Nat} {p : Addr}
    (T : TabS G f j S s p) {Gs : Spec.Mgf1.Hash}
    (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = G.D) (hGv : Proof.Mgf1.Valid Gs)
    {src srcLen dst dstLen : Nat} (hf : MFit src srcLen dst dstLen) {t : State} (h : Base S vf s t)
    (hsy : t.syms = s.syms)
    (h6 : t.gpr .s6 = off (S s) src) (h7 : t.gpr .s7 = BitVec.ofNat 64 srcLen) (h8 : t.gpr .s8 = off (S s) dst)
    (h9 : t.gpr .s9 = BitVec.ofNat 64 dstLen) :
    WP isa (mgfXorT f j) t fun t' => (Base S vf s t' ∧ ∀ o, Kp o → view t'.mem (S s) o =
      mixV (view t.mem (S s)) (Spec.Mgf1.mgf1 Gs (srcB (view t.mem (S s)) src srcLen) dstLen) dst dstLen o) ∧
      t'.syms = s.syms := by
  have hpos := hf.pos
  have hD : 0 < G.D := hG.hD0
  refine WP.seq (WP.of_syms (wp_li (imm := 0) (by decide) fun t₁ o₁ e₁ => wp_li (imm := 0) (by decide)
    fun t₂ o₂ e₂ => wp_nil fun sy₂ => ?_))
  have k₂ : Only [.s10, .s11] t t₂ := (o₁.trans o₂).mono
  have I0 : MgfIT S vf s (view t.mem (S s)) (Spec.Mgf1.mgf1 Gs (srcB (view t.mem (S s)) src srcLen) dstLen) src
      srcLen dst dstLen G.D 0 t₂ :=
    ⟨h.only P k₂, by rw [k₂.get .s6, h6], by rw [k₂.get .s7, h7], by rw [k₂.get .s8, h8],
      by rw [k₂.get .s9, h9], by rw [o₂.get .s10, e₁], by rw [e₂, Nat.zero_mul],
      fun o _ => by rw [mixV, ifn (by omega), k₂.mem], sy₂.trans hsy⟩
  refine WP.loop (M := isa) (fun n w => ∃ c, n = dstLen - c * G.D ∧ c * G.D < dstLen ∧
      MgfIT S vf s (view t.mem (S s)) (Spec.Mgf1.mgf1 Gs (srcB (view t.mem (S s)) src srcLen) dstLen) src srcLen dst
        dstLen G.D c w)
    ?_ (dstLen - 0 * G.D) t₂ ⟨0, rfl, by omega, I0⟩
  rintro n w ⟨c, rfl, hc, I⟩
  refine WP.mono (roundT_ok P hG hF T hGh hGl hGv hf I hc) fun w' ⟨hcf, I'⟩ => ?_
  have hs1 : (c + 1) * G.D = c * G.D + G.D := Nat.succ_mul _ _
  by_cases h' : (c + 1) * G.D < dstLen
  · exact .inr ⟨by rw [eval_nonzero, hcf, decide_eq_true h'], _, by omega, c + 1, rfl, h', I'⟩
  · exact .inl ⟨by rw [eval_nonzero, hcf, decide_eq_false h'], ⟨I'.base,
      fun o ho => by rw [I'.em o ho, Nat.min_eq_right (by omega)]⟩, I'.sy⟩

end

end VG.Proof.RsaOaep.RISCV64
