module

public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.MgfSteps
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.MgfArith
public import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.View
import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Encode

/-!
# RSAES-OAEP on PPC64LE: MGF1's blocks, with the hash function of a table

Untrusted: everything here is checked by Lean. The blocks of MGF1's round
(`Impl.RsaOaep.PPC64LE.roundT`) between the calls: the counter written
big-endian to `S + oCtr` (`ctr_ok`, as `ctrV`), the selection of how many
digest bytes go into `dst` (`xorHeadT_ok`), their exclusive-or into it
(`xorLoop_ok`), and the next counter (`nextCtrT_ok`). MGF1's hash function
is that of the table that is our stack argument `j` (`TabS`: what the table
holds on entry, where nothing we write reaches it), whose words a load
through the stack argument reads (`wp_tword`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE VG.WriteBytes
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep MemTo wp_li wp_addi wp_subi wp_add wp_sub wp_and wp_xor wp_mov wp_lsr
  wp_stb wp_lbz wp_nil wp_countdown ofNat_succ' wp_addSp wp_ld)
open VG.Impl.Hmac.Stream.PPC64LE (Hash)

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
the argument and the table readable, and apart from what we write (`kR s`,
our part of the working space); the table holding `G`'s functions'
addresses (an indirect call reaching them) and its digest length. -/
structure TabS (G : Hash) (f : Fns) (j : Nat) (S : State → Addr) (s : State) (p : Addr) : Prop where
  jo : arg j < 2 ^ 15 ∧ arg j % 4 = 0
  arg : s.mem.readW (stackArgAddr s j) 64 = p
  argR : InRegions s.rd (stackArgAddr s j) 8
  argK : Region.Disjoint ⟨stackArgAddr s j, 8⟩ (kR s)
  argS : Region.Disjoint ⟨stackArgAddr s j, 8⟩ (SC S s)
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
  refine ⟨T.jo, ?_, by rw [hrd, eA]; exact T.argR, by rw [eA, eK]; exact T.argK, by rw [eA, hS]; exact T.argS,
    fun k hk => by rw [hrd]; exact T.tR k hk, fun k hk => by rw [eK]; exact T.tK k hk,
    fun k hk => by rw [hS]; exact T.tS k hk, ⟨?_, ?_, ?_⟩, ?_, by rw [hsy]; exact T.ok⟩
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

/-- The table's word `k` into `d`, through our stack argument `j`. -/
theorem wp_tword {G : Hash} {f : Fns} {j : Nat} {S : State → Addr} {vf : State → Reg → BitVec 64} {s t : State}
    {p : Addr} (T : TabS G f j S s p) (h : Base S vf s t) {k : Nat} (hk : k < 5) {d : Reg} (hd : d ≠ .r0)
    {is : List Instr} {Q : State → Prop}
    (kk : ∀ t', Only [d] t t' → t'.gpr d = s.mem.readW (p + BitVec.ofNat 64 (8 * k)) 64 → WP isa (.block is) t' Q) :
    WP isa (.block (tword d j k ++ is)) t Q := by
  simp only [tword, List.cons_append, List.nil_append]
  refine wp_addSp fun u₁ o₁ e₁ => wp_ld (a := stackArgAddr s j) (by rw [e₁, h.sp, BitVec.add_zero, stackArgAddr_fb])
    (by rw [o₁.rd, h.rd]; exact let ⟨R, hR, hc⟩ := T.argR; ⟨R, List.mem_append_left _ hR, hc⟩)
    (fun u₂ o₂ e₂ => wp_ld (a := p + BitVec.ofNat 64 (8 * k)) (by rw [e₂, o₁.mem, h.readW_apart T.argK T.argS, T.arg])
      (by rw [o₂.rd, o₁.rd, h.rd]; exact let ⟨R, hR, hc⟩ := T.tR k hk; ⟨R, List.mem_append_left _ hR, hc⟩)
      (fun u₃ o₃ e₃ => kk u₃ ((o₁.trans (o₂.trans o₃)).mono fun r hr => by
        simp only [List.mem_append, List.mem_singleton, or_self] at hr ⊢; exact hr) (by
        rw [e₃, o₂.mem, o₁.mem, h.readW_apart (T.tK k hk) (T.tS k hk)])) hd (by omega)) hd T.jo

open VG.Proof.RsaPkcs1Sig (bytesAt_length writeBytes_out)
open VG.Proof.Mgf1 (ifp ifn)

section
variable {S : State → Addr} {vf : State → Reg → BitVec 64} {s : State} (P : Fits S s)
include P

end

/-- How many bytes of the digest go into `dst`: `min(hLen, dstLen - done)`,
`hLen` the table's word 4. -/
theorem xorHeadT_ok {G : Hash} {f : Fns} {j : Nat} {S' : State → Addr} {vf : State → Reg → BitVec 64} {s₀ : State}
    {p : Addr} (T : TabS G f j S' s₀ p) {t : State} (hb : Base S' vf s₀ t) {S : Addr}
    {dst dstLen done : Nat}
    (hD : G.D < 2 ^ 15) (h14 : t.gpr .r14 = S) (h26 : t.gpr .r26 = off S dst) (h27 : t.gpr .r27 = BitVec.ofNat 64 dstLen)
    (h29 : t.gpr .r29 = BitVec.ofNat 64 done) (hlt : done < dstLen) (hdl : dstLen < 2 ^ 63) :
    WP isa (.block (xorHeadT j)) t fun t' => Only [.r6, .r7, .r8, .r9, .r10, .r11, .r12] t t' ∧
      t'.gpr .r11 = off S oDig ∧ t'.gpr .r12 = off S (dst + done) ∧
      t'.gpr .r9 = BitVec.ofNat 64 (min G.D (dstLen - done)) := by
  simp only [xorHeadT]
  refine wp_tword T hb (k := 4) (by decide) (by decide) fun u₀ o₀ e₀ => ?_
  rw [show 8 * 4 = 32 from rfl, T.d] at e₀
  refine wp_addi fun u₁ o₁ e₁ => wp_add fun u₂ o₂ e₂ => wp_sub fun u₃ o₃ e₃ => ?_
  refine wp_sub fun u₅ o₅ e₅ => wp_lsr fun u₆ o₆ e₆ => wp_li (by decide) fun u₇ o₇ e₇ => wp_sub fun u₈ o₈ e₈ =>
    wp_and fun u₉ o₉ e₉ => wp_add fun u₁₀ o₁₀ e₁₀ => wp_nil ?_
  have k : Only [.r6, .r7, .r8, .r9, .r10, .r11, .r12] t u₁₀ :=
    (o₀.trans (o₁.trans (o₂.trans (o₃.trans (o₅.trans (o₆.trans (o₇.trans (o₈.trans (o₉.trans o₁₀))))))))).mono
  have r8 : u₃.gpr .r8 = BitVec.ofNat 64 (dstLen - done) := by
    rw [e₃, o₂.get .r27, o₂.get .r29, o₁.get .r27, o₁.get .r29, o₀.get .r27, o₀.get .r29, h27, h29,
      Offset.ofNat_sub_ofNat (by omega_arith)]
  have r9 : u₃.gpr .r9 = BitVec.ofNat 64 G.D := by rw [o₃.get .r9, o₂.get .r9, o₁.get .r9, e₀]
  have r10 : u₅.gpr .r10 = BitVec.ofNat 64 (dstLen - done) - BitVec.ofNat 64 G.D := by
    rw [e₅, r8, r9]
  refine ⟨k, ?_, ?_, ?_⟩
  · rw [o₁₀.get .r11, o₉.get .r11, o₈.get .r11, o₇.get .r11, o₆.get .r11, o₅.get .r11, o₃.get .r11,
      o₂.get .r11, e₁, o₀.get .r14, h14]
  · rw [o₁₀.get .r12, o₉.get .r12, o₈.get .r12, o₇.get .r12, o₆.get .r12, o₅.get .r12, o₃.get .r12, e₂,
      o₁.get .r26, o₁.get .r29, o₀.get .r26, o₀.get .r29, h26, h29, off_add]
  · rw [e₁₀, o₉.get .r9, o₈.get .r9, o₇.get .r9, o₆.get .r9, o₅.get .r9, r9, e₉, o₈.get .r10, o₇.get .r10,
      o₆.get .r10, r10, e₈, e₇, o₇.get .r6, e₆, r10]
    exact minSel (by omega_arith) (by omega_arith)

/-- `nextCtrT`: the next counter and `done`, and in `r12` whether `done` is
still below `dstLen`. -/
theorem nextCtrT_ok {G : Hash} {f : Fns} {j : Nat} {S' : State → Addr} {vf : State → Reg → BitVec 64} {s₀ : State}
    {p : Addr} (T : TabS G f j S' s₀ p) {t : State} (hb : Base S' vf s₀ t) {c done dstLen : Nat}
    (h28 : t.gpr .r28 = BitVec.ofNat 64 c) (h29 : t.gpr .r29 = BitVec.ofNat 64 done)
    (h27 : t.gpr .r27 = BitVec.ofNat 64 dstLen) (hd : done + G.D < 2 ^ 63) (hdl : dstLen < 2 ^ 63) :
    WP isa (.block (nextCtrT j)) t fun t' => Only [.r28, .r29, .r12] t t' ∧
      t'.gpr .r28 = BitVec.ofNat 64 (c + 1) ∧ t'.gpr .r29 = BitVec.ofNat 64 (done + G.D) ∧
      (t'.gpr .r12 != 0) = decide (done + G.D < dstLen) := by
  simp only [nextCtrT]
  refine wp_tword T hb (k := 4) (by decide) (by decide) fun u₀ o₀ e₀ => ?_
  rw [show 8 * 4 = 32 from rfl, T.d] at e₀
  refine wp_addi fun u₁ o₁ e₁ => wp_add fun u₂ o₂ e₂ => wp_sub fun u₃ o₃ e₃ => wp_lsr fun u₄ o₄ e₄ =>
    wp_nil ⟨(o₀.trans (o₁.trans (o₂.trans (o₃.trans o₄)))).mono, ?_, ?_, ?_⟩
  · rw [o₄.get .r28, o₃.get .r28, o₂.get .r28, e₁, o₀.get .r28, h28, BitVec.ofNat_add]
  · rw [o₄.get .r29, o₃.get .r29, e₂, o₁.get .r29, o₁.get .r12, o₀.get .r29, h29, e₀, BitVec.ofNat_add]
  · rw [e₄, e₃, o₂.get .r27, e₂, o₁.get .r29, o₁.get .r27, o₁.get .r12, o₀.get .r29, o₀.get .r27, h29, h27, e₀,
      ← BitVec.ofNat_add]
    exact ne_zero_ltBit hd hdl

end VG.Proof.RsaOaep.PPC64LE
