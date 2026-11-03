module

public import VerifiedGarbage.Proof.RsaOaep.AArch64.Mgf
public import VerifiedGarbage.Impl.RsaOaep.AArch64
public import VerifiedGarbage.Proof.Framework.ICall
public import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# RSAES-OAEP on AArch64: MGF1 with the hash function of a table

As on x86-64 (`Proof/RsaOaep/X86_64/MgfT.lean`): `Table.mgfXor lay sArg sTab
sD f` (`Impl/RsaOaep/AArch64/Mgf1/Table.lean`) XORs `MGF1(src, dstLen)` into
`dst` as `mgfXor lay G` does (`mgfXorT_ok`, as `mgfXor_ok`), for `G` the hash
function whose functions' addresses the table holds (`Tab`): the table's
address is in the slot `sTab` (word 32) and `G`'s digest length in `sD`
(word 33), and the table holds the addresses of `G`'s `init`, `update` and
`finalize`, which an indirect call of `f`'s functions reaches (`TabOK`), in
every memory that differs from the entry state's only where MGF1 may write
(`mgfRs`: the frame, the working space and the 16 bytes below the frame, as
`Step` says). So each indirect call (`tcall`) runs as `G`'s call (`initT_ok`,
`updT_ok`, `finT_ok`, from `init_ok`, `upd_ok`, `fin_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.AArch64.Table

open VG VG.AArch64 VG.Impl.RsaOaep.AArch64 VG.Proof.RsaOaep.AArch64
open VG.Impl.RsaOaep.AArch64.Mgf1.Table (Fns tcall tabArg tabHead)
open VG.Impl.RsaOaep.AArch64.Mgf1 (seqs initArgs updSrcArgs updCtrArgs finArgs xorBody)
open VG.Proof.Mgf1 (ifp ifn)
open VG.Impl.Pbkdf2.Md.AArch64 (Stream Hash)
open VG.Proof.Pbkdf2.Md.AArch64.Calls (StreamOK VecKept)

/-! ## The table -/

/-- At `p` in `m`, the addresses `sy` gives `G`'s `init`, `update` and
`finalize`. -/
def TabMem (G : Stream) (sy : String → Addr) (p : Addr) (m : Mem) : Prop :=
  m.readW (off p (8 * 0)) 64 = sy G.initN ∧ m.readW (off p (8 * 1)) 64 = sy G.updN ∧
    m.readW (off p (8 * 2)) 64 = sy G.finN

/-- An indirect call of `f`'s functions, at the addresses `sy` gives, to the
address of one of `G`'s functions reaches it. -/
structure TabOK (G : Stream) (f : Fns) (sy : String → Addr) : Prop where
  i : f.init.find? (fun q => sy q.1 == sy G.initN) = some (G.initN, G.initC)
  u : f.upd.find? (fun q => sy q.1 == sy G.updN) = some (G.updN, G.updC)
  f : f.fin.find? (fun q => sy q.1 == sy G.finN) = some (G.finN, G.finC)

/-- Where MGF1 may write: its frame, its working space and the 16 bytes
below the frame (`Step`'s frame). -/
abbrev mgfRs (F S : Addr) : List Region := [⟨F, frameBytes⟩, ⟨S, oRsa⟩, retR F]

/-- The table at `p`, from MGF1's entry state `u` with its frame at `F` and
working space at `S`, the word at `F + sArg` its address: readable, and
holding `G`'s functions' addresses and its digest length, and that word `p`,
in every memory that differs from `u`'s only within `mgfRs`. -/
structure Tab (G : Stream) (f : Fns) (F S p : Addr) (sArg : Nat) (u : State) : Prop where
  ok : TabOK G f u.syms
  rd : ∀ j < 3, InRegions (u.rd ++ u.wr) (off p (8 * j)) 8
  rdD : InRegions (u.rd ++ u.wr) (off p 32) 8
  rdA : InRegions (u.rd ++ u.wr) (off F sArg) 8
  mem : ∀ m, Frame (mgfRs F S) u.mem m → TabMem G u.syms p m ∧
    m.readW (off p 32) 64 = BitVec.ofNat 64 G.D ∧ m.readW (off F sArg) 64 = p

/-- The table, from a later state of the same frame. -/
theorem Tab.step {G : Stream} {f : Fns} {F S p : Addr} {sArg : Nat} {u v : State} (T : Tab G f F S p sArg u)
    (st : Step F S [] u v) (sy : v.syms = u.syms) : Tab G f F S p sArg v :=
  ⟨by rw [sy]; exact T.ok, by rw [st.rd, st.wr]; exact T.rd, by rw [st.rd, st.wr]; exact T.rdD,
    by rw [st.rd, st.wr]; exact T.rdA, fun m hm => by rw [sy]; exact T.mem m (st.frame.trans hm)⟩

/-- The table at `p`, in the state `t`. -/
structure TabAt (G : Stream) (f : Fns) (p : Addr) (t : State) : Prop where
  ok : TabOK G f t.syms
  rd : ∀ j < 3, InRegions (t.rd ++ t.wr) (off p (8 * j)) 8
  mem : TabMem G t.syms p t.mem

theorem Tab.at {G : Stream} {f : Fns} {F S p : Addr} {sArg : Nat} {u₀ v : State} (T : Tab G f F S p sArg u₀)
    (st : Step F S [] u₀ v) (sy : v.syms = u₀.syms) : TabAt G f p v :=
  ⟨by rw [sy]; exact T.ok, by rw [st.rd, st.wr]; exact T.rd, by rw [sy]; exact (T.mem _ st.frame).1⟩

/-! ## The calls -/

/-- The indirect call of the table's function `j`, at the address `p`'s word
`j` holds, of `n`: from the state after the address's load, which keeps
`Step`, memory, the addresses of statics and the arguments in `x0`–`x4`. -/
theorem tcall_ok {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep t.mem F S V W) {p : Addr} (hp : W 32 = p) {j : Nat} (hj : j < 3) {n : String} {c : Prog isa}
    {ts : List (String × Prog isa)} (hrd : InRegions (t.rd ++ t.wr) (off p (8 * j)) 8)
    (hw : t.mem.readW (off p (8 * j)) 64 = t.syms n)
    (hf : ts.find? (fun q => t.syms q.1 == t.syms n) = some (n, c)) {Q : State → Prop}
    (h : ∀ t', Step F S [] t t' → t'.mem = t.mem → t'.syms = t.syms → t'.gpr .x0 = t.gpr .x0 →
      t'.gpr .x1 = t.gpr .x1 → t'.gpr .x2 = t.gpr .x2 → t'.gpr .x3 = t.gpr .x3 → t'.gpr .x4 = t.gpr .x4 →
      WP isa (.call n c) t' Q) :
    WP isa (tcall sTab j ts) t Q := by
  have h256 : InRegions (t.rd ++ t.wr) (F + BitVec.ofNat 64 256) 8 := L.ld (d := 256) (by decide)
  have r32 := R.rd8 (d := 256) (k := 32) rfl (by decide) hp
  have hj' : 8 * j < 32768 := by omega
  refine WP.seq (WP.mono (Q := fun (t' : State) => Step F S [] t t' ∧ t'.mem = t.mem ∧ t'.syms = t.syms ∧
      t'.gpr .x0 = t.gpr .x0 ∧ t'.gpr .x1 = t.gpr .x1 ∧ t'.gpr .x2 = t.gpr .x2 ∧ t'.gpr .x3 = t.gpr .x3 ∧
      t'.gpr .x4 = t.gpr .x4 ∧ t'.gpr .x16 = t.syms n) ?_
    fun t' ⟨st, hm, hs, h0, h1, h2, h3, h4, h16⟩ => ?_)
  · have hw' : t.mem.read (p + BitVec.ofNat 64 (8 * j)) 8 = t.syms n := by simpa [Mem.readW] using hw
    oaep_run [tcall, sTab, h256, L.sp, r32, hrd, hw', hj', Nat.mul_mod_right]
    oaep_fin
  · refine WP.icalls_of_call (a := t.syms n) (by simp only [icall, h16]) ?_
      (h t' st hm hs h0 h1 h2 h3 h4)
    show ts.find? (fun q => isa.fnAddr t' q.1 == t.syms n) = _
    simp only [isa]; rw [hs]; exact hf

variable {G : Stream} (hG : StreamOK G) {f : Fns}

include hG in
theorem initT_ok {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep t.mem F S V W) {p : Addr} (hp : W 32 = p) (T : TabAt G f p t) (h0 : t.gpr .x0 = off S oSt) :
    WP isa (tcall sTab 0 f.init) t fun t' => Lay t' F S ∧ Step F S [] t t' ∧
      Rep t'.mem F S (fun o => if inR [(oSt, G.S)] o then t'.mem (off S o) else V o) W ∧
      hG.SH.Repr t'.mem (off S oSt) [] :=
  tcall_ok L R hp (by decide) (T.rd 0 (by decide)) T.mem.1 T.ok.i fun u st hm _ x0 _ _ _ _ =>
    WP.mono (init_ok hG (L.congr st.sp st.wr (by rw [hm])) (hm ▸ R) (x0.trans h0) [])
      fun t' ⟨L', S', R', hr'⟩ => ⟨L', st.trans S', R', hr'⟩

include hG in
theorem updT_ok {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep t.mem F S V W) {p : Addr} (hp : W 32 = p) (T : TabAt G f p t) {a len : Nat} (ha : a + len ≤ oRsa)
    (hda : a + len ≤ oSt ∨ oSt + G.S ≤ a) (hwa : a + len ≤ oW ∨ oW + hG.Wb ≤ a)
    (h0 : t.gpr .x0 = off S oSt) (h2 : t.gpr .x2 = off S a) (h3 : t.gpr .x3 = BitVec.ofNat 64 len)
    (h4 : t.gpr .x4 = off S oW) :
    WP isa (tcall sTab 1 f.upd) t fun t' => Lay t' F S ∧ Step F S [] t t' ∧
      Rep t'.mem F S (fun o => if inR [(oSt, G.S), (oW, hG.Wb)] o then t'.mem (off S o) else V o) W ∧
      (∀ m, hG.SH.Repr t.mem (off S oSt) m → t.gpr .x1 = BitVec.ofNat 64 m.length →
        hG.SH.Repr t'.mem (off S oSt) (m ++ (List.range len).map fun i => V (a + i))) :=
  tcall_ok L R hp (by decide) (T.rd 1 (by decide)) T.mem.2.1 T.ok.u fun u st hm _ x0 x1 x2 x3 x4 =>
    WP.mono (upd_ok hG (L.congr st.sp st.wr (by rw [hm])) (hm ▸ R) ha hda hwa (x0.trans h0) (x2.trans h2)
        (x3.trans h3) (x4.trans h4) [])
      fun t' ⟨L', S', R', hr'⟩ => ⟨L', st.trans S', R', fun m hm' hc => hr' m (hm ▸ hm') (x1.trans hc)⟩

include hG in
theorem finT_ok {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep t.mem F S V W) {p : Addr} (hp : W 32 = p) (T : TabAt G f p t) {o : Nat}
    (ho : o + 64 ≤ oSt ∨ (oSt + 256 ≤ o ∧ o + 64 ≤ oW))
    (h0 : t.gpr .x0 = off S oSt) (h2 : t.gpr .x2 = off S o) (h3 : t.gpr .x3 = off S oW) :
    WP isa (tcall sTab 2 f.fin) t fun t' => Lay t' F S ∧ Step F S [] t t' ∧
      Rep t'.mem F S (fun x => if inR [(oSt, G.S), (o, G.F), (oW, hG.Wb)] x then t'.mem (off S x) else V x) W ∧
      (∀ m, hG.SH.Repr t.mem (off S oSt) m → m.length < 2 ^ 64 → t.gpr .x1 = BitVec.ofNat 64 m.length →
        ∀ i < G.D, t'.mem (off S (o + i)) = (hG.SH.H.hash m).getD i 0) :=
  tcall_ok L R hp (by decide) (T.rd 2 (by decide)) T.mem.2.2 T.ok.f fun u st hm _ x0 x1 x2 x3 _ =>
    WP.mono (fin_ok hG (L.congr st.sp st.wr (by rw [hm])) (hm ▸ R) ho (x0.trans h0) (x2.trans h2) (x3.trans h3) [])
      fun t' ⟨L', S', R', hr'⟩ => ⟨L', st.trans S', R', fun m hm' hl hc => hr' m (hm ▸ hm') hl (x1.trans hc)⟩

/-! ## The digest into `dst` -/

theorem xorHeadT_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {D dst dstLen done : Nat} (hD : D < 2 ^ 64) (hdl : dstLen < 2 ^ 64)
    (h33 : W 33 = BitVec.ofNat 64 D)
    (he : W 15 = off S dst) (hdb : W 16 = BitVec.ofNat 64 dstLen) (hdn : W 18 = BitVec.ofNat 64 done)
    (hlt : done < dstLen) (ws : List Region) :
    WP isa (.block (Impl.RsaOaep.AArch64.Mgf1.Table.xorHead lay sD)) u fun u' => Step F S ws u u' ∧
      u'.mem = u.mem ∧ u'.gpr .x11 = off S oDig ∧
      u'.gpr .x12 = off S (dst + done) ∧ u'.gpr .x14 = BitVec.ofNat 64 (min D (dstLen - done)) := by
  have h96 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 96) 8 := L.ld (d := 96) (by decide)
  have h120 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 120) 8 := L.ld (d := 120) (by decide)
  have h128 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 128) 8 := L.ld (d := 128) (by decide)
  have h144 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 144) 8 := L.ld (d := 144) (by decide)
  have h264 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 264) 8 := L.ld (d := 264) (by decide)
  have hs : u.mem.read (F + BitVec.ofNat 64 96) 8 = S := L.slot
  have r15 := R.rd8 (d := 120) (k := 15) rfl (by decide) he
  have r16 := R.rd8 (d := 128) (k := 16) rfl (by decide) hdb
  have r18 := R.rd8 (d := 144) (k := 18) rfl (by decide) hdn
  have r33 := R.rd8 (d := 264) (k := 33) rfl (by decide) h33
  refine WP.mono (Q := fun (u' : State) => u'.mem = u.mem ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp ∧
      u'.v = u.v ∧ (∀ r ∈ preserved, r ≠ .x30 → u'.gpr r = u.gpr r) ∧ u'.gpr .x11 = off S oDig ∧
      u'.gpr .x12 = off S dst + BitVec.ofNat 64 done ∧
      u'.gpr .x14 = if (BitVec.ofNat 64 D).toNat ≤ (BitVec.ofNat 64 (dstLen - done)).toNat then
        BitVec.ofNat 64 D else BitVec.ofNat 64 (dstLen - done)) ?_
    fun u' ⟨hm, hrd, hwr, hsp, hv, hcs, x11, x12, x14⟩ => ⟨Step.blk ws hrd hwr hsp hv hcs hm, hm, x11,
      x12.trans (off_off S dst done), by
        rw [x14, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hD,
          Nat.mod_eq_of_lt (show dstLen - done < 2 ^ 64 by omega_using [hdl])]
        split <;> (congr 1; omega_arith)⟩
  oaep_run [Impl.RsaOaep.AArch64.Mgf1.Table.xorHead, Mgf1.scr, lay, sScr, sDst, sDstLen, sDone, sD, oDig, h96,
    h120, h128, h144, h264, L.sp, hs, r15, r16, r18, r33,
    Offset.ofNat_sub_ofNat (show done ≤ dstLen by omega_using [hlt]), carry_sub, decide_eq_true_eq]
  oaep_fin

theorem xorOutT_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {D dst dstLen done : Nat} (hfit : dst + dstLen ≤ oSt) (hD : 0 < D)
    (hDF : D ≤ 64) (h33 : W 33 = BitVec.ofNat 64 D) (he : W 15 = off S dst) (hdb : W 16 = BitVec.ofNat 64 dstLen)
    (hdn : W 18 = BitVec.ofNat 64 done) (hlt : done < dstLen) (ws : List Region) :
    WP isa (Impl.RsaOaep.AArch64.Mgf1.Table.xorOut lay sD) u fun u' => Lay u' F S ∧ Step F S ws u u' ∧
      Rep u'.mem F S (xorV V oDig (dst + done) (min D (dstLen - done))) W := by
  have c1 : oSt = 3072 := rfl
  have c3 : oDig = 3328 := rfl
  have c5 : oRsa = 8192 := rfl
  refine WP.seq (WP.mono (xorHeadT_ok L R (D := D) (by omega_using [hDF]) (by omega_using [hfit, c1]) h33 he hdb
    hdn hlt ws) fun v ⟨Sv, hm, x11, x12, x14⟩ => ?_)
  have Lv : Lay v F S := L.congr Sv.sp Sv.wr (by rw [hm])
  have Rv : Rep v.mem F S V W := hm ▸ R
  refine WP.mono (xorLoop_ok Lv Rv (a := oDig) (b := dst + done) (n := min D (dstLen - done))
    (by omega_using [hD, hlt]) (by omega_using [hDF, c3, c5]) (by omega_using [hfit, hlt, c1, c5])
    (by omega_using [hfit, c1, c3]) x11 x12 x14 ws) fun w ⟨Lw, Sw, Rw⟩ => ⟨Lw, Sv.trans Sw, Rw⟩

/-! ## The next counter -/

theorem nextCtrT_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {D c done dstLen : Nat} (hc : W 17 = BitVec.ofNat 64 c)
    (hdn : W 18 = BitVec.ofNat 64 done) (hdb : W 16 = BitVec.ofNat 64 dstLen) (h33 : W 33 = BitVec.ofNat 64 D)
    (hd' : done + D < 2 ^ 32) (hdb' : dstLen < 2 ^ 32) (ws : List Region) :
    WP isa (.block (Impl.RsaOaep.AArch64.Mgf1.Table.nextCtr lay sD)) u fun u' => Lay u' F S ∧ Step F S ws u u' ∧
      (u'.gpr .x12 != 0) = decide (done + D < dstLen) ∧
      Rep u'.mem F S V (upd (upd W 17 (BitVec.ofNat 64 (c + 1))) 18 (BitVec.ofNat 64 (done + D))) := by
  have G' := L.geo
  have R1 : Rep (u.mem.write (off F 136) 8 (BitVec.ofNat 64 (c + 1))) F S V (upd W 17 (BitVec.ofNat 64 (c + 1))) :=
    R.wq G' (k := 17) (by decide) _
  have R2 : Rep ((u.mem.write (off F 136) 8 (BitVec.ofNat 64 (c + 1))).write (off F 144) 8
      (BitVec.ofNat 64 (done + D))) F S V
      (upd (upd W 17 (BitVec.ofNat 64 (c + 1))) 18 (BitVec.ofNat 64 (done + D))) :=
    R1.wq G' (k := 18) (by decide) _
  have h136 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 136) 8 := L.ld (d := 136) (by decide)
  have h144 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 144) 8 := L.ld (d := 144) (by decide)
  have h128 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 128) 8 := L.ld (d := 128) (by decide)
  have h264 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 264) 8 := L.ld (d := 264) (by decide)
  have w136 : InRegions u.wr (F + BitVec.ofNat 64 136) 8 := L.st (d := 136) (by decide)
  have w144 : InRegions u.wr (F + BitVec.ofNat 64 144) 8 := L.st (d := 144) (by decide)
  have rc := R.rd8 (d := 136) (k := 17) rfl (by decide) hc
  have rd1 := R1.rd8 (d := 144) (k := 18) rfl (by decide) (show upd W 17 _ 18 = _ by simp only [upd]; exact hdn)
  have rD1 := R1.rd8 (d := 264) (k := 33) rfl (by decide) (show upd W 17 _ 33 = _ by simp only [upd]; exact h33)
  have rl2 := R2.rd8 (d := 128) (k := 16) rfl (by decide) (show upd (upd W 17 _) 18 _ 16 = _ by simp only [upd]; exact hdb)
  refine WP.mono (Q := fun (u' : State) => u'.mem = (u.mem.write (off F 136) 8 (BitVec.ofNat 64 (c + 1))).write
      (off F 144) 8 (BitVec.ofNat 64 (done + D)) ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp ∧ u'.v = u.v ∧
      (∀ r ∈ preserved, r ≠ .x30 → u'.gpr r = u.gpr r) ∧
      u'.gpr .x12 = if (BitVec.ofNat 64 dstLen).toNat ≤ (BitVec.ofNat 64 (done + D)).toNat then 0
        else BitVec.allOnes 64) ?_
    fun u' ⟨hm, hrd, hwr, hsp, hv, hcs, x12⟩ => ?_
  · oaep_run [Impl.RsaOaep.AArch64.Mgf1.Table.nextCtr, lay, sCtr, sDone, sDstLen, sD, h136, h144, h128, h264,
      w136, w144, L.sp, BitVec.add_zero, rc, rd1, rD1, rl2, BitVec.ofNat_add_ofNat, sbc_self]
    oaep_fin
  have R' : Rep u'.mem F S V (upd (upd W 17 (BitVec.ofNat 64 (c + 1))) 18 (BitVec.ofNat 64 (done + D))) := by
    rw [hm]; exact R2
  refine ⟨L.congr hsp hwr ?_, ⟨hrd, hwr, hsp, hcs, fun r _ => by rw [hv], ?_⟩, ?_, R'⟩
  · rw [show sScr = 8 * 12 from rfl, R'.fr 12 (by decide), R.fr 12 (by decide)]; rfl
  · rw [hm]
    exact (Frame.write (Frame.write (Frame.refl _ _) (List.mem_cons_self ..) _ (cF F (by decide)))
      (List.mem_cons_self ..) _ (cF F (by decide)))
  · rw [x12, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hdb']),
      Nat.mod_eq_of_lt (by omega_using [hd'])]
    by_cases h : dstLen ≤ done + D
    · rw [ifp h]; simp only [bne_self_eq_false]; exact (decide_eq_false (by omega_using [h])).symm
    · rw [ifn h]; exact (decide_eq_true (by omega_using [h])).symm

/-! ## One counter -/

/-- A piece's `WP`, with the addresses of statics kept. -/
theorem wp_sy {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q) :
    WP isa c s fun s' => Q s' ∧ s'.syms = s.syms :=
  WP.mono_syms h fun _ q sy => ⟨q, sy⟩

include hG in
theorem roundT_ok {Gs : Spec.Mgf1.Hash} (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = G.D)
    (hGv : Proof.Mgf1.Valid Gs) {u₀ : State} {F S p : Addr} {sArg : Nat} (T : Tab G f F S p sArg u₀)
    {V : Nat → Byte} {W : Nat → BitVec 64} {src srcLen dst dstLen c : Nat} (hf : MFit src srcLen dst dstLen)
    (A : MArgs W S src srcLen dst dstLen) (h32 : W 32 = p) (h33 : W 33 = BitVec.ofNat 64 G.D)
    {v : State} (I : MgfI u₀ F S V W (Spec.Mgf1.mgf1 Gs (srcB V src srcLen) dstLen) dst dstLen G.D c v)
    (sy : v.syms = u₀.syms) (hc : c * G.D < dstLen) :
    WP isa (Impl.RsaOaep.AArch64.Mgf1.Table.round lay sTab sD f) v fun v' =>
      (v'.gpr .x12 != 0) = decide ((c + 1) * G.D < dstLen) ∧
      MgfI u₀ F S V W (Spec.Mgf1.mgf1 Gs (srcB V src srcLen) dstLen) dst dstLen G.D (c + 1) v' ∧
      v'.syms = u₀.syms := by
  obtain ⟨hzS, hzF, hzW, hzDF, hzD⟩ := sizes hG
  have c1 : oSt = 3072 := rfl
  have c2 : oDig = 3328 := rfl
  have c3 : oCtr = 3456 := rfl
  have c4 : oW = 3520 := rfl
  have c5 : oRsa = 8192 := rfl
  have hfs := hf.fs
  have hfd := hf.fd
  have hsep := hf.sep
  have hdb := hf.dstB
  have hcD : c ≤ c * G.D := Nat.le_mul_of_pos_right c hzD
  obtain ⟨V1, W1, R1, h17, h18, hW, hV⟩ := I.rep
  have A1 : MArgs W1 S src srcLen dst dstLen := A.of_eq fun k h1 h2 => hW k (by unfold nW frameBytes; omega_using [h2])
    (by omega_using [h2]) (by omega_using [h2])
  have w32 : W1 32 = p := (hW 32 (by decide) (by decide) (by decide)).trans h32
  have w33 : W1 33 = BitVec.ofNat 64 G.D := (hW 33 (by decide) (by decide) (by decide)).trans h33
  have hsrc1 : ∀ i < srcLen, V1 (src + i) = V (src + i) := fun i hi => by
    rw [hV _ (by omega_using [c1, c5, hfs, hi]) ((mOut_iff _).mpr (by omega_using [hfs, hi])), mixV,
      ifn (by omega_using [hsep, hi])]
  unfold Impl.RsaOaep.AArch64.Mgf1.Table.round seqs seqs seqs seqs seqs seqs seqs seqs seqs seqs
  -- `init`.
  refine WP.seq (WP.mono (wp_sy (initArgs_ok I.L [])) fun u1 ⟨⟨S1, hm1, x01⟩, s1⟩ => ?_)
  have L1 : Lay u1 F S := I.L.congr S1.sp S1.wr (by rw [hm1])
  have R1' : Rep u1.mem F S V1 W1 := hm1 ▸ R1
  have st1 := I.st.trans S1
  have sy1 := s1.trans sy
  refine WP.seq (WP.mono (wp_sy (initT_ok hG L1 R1' w32 (T.at st1 sy1) x01)) fun u2 ⟨⟨L2, S2, R2, hr2⟩, s2⟩ => ?_)
  have st2 := st1.trans S2
  have sy2 := s2.trans sy1
  obtain ⟨V2, R2, hV2, -⟩ := Rep.ex R2
  -- `update` with `src`.
  refine WP.seq (WP.mono (wp_sy (updSrc_ok L2 R2 A1 [])) fun u3 ⟨⟨S3, hm3, x03, x13, x23, x33, x43⟩, s3⟩ => ?_)
  have L3 : Lay u3 F S := L2.congr S3.sp S3.wr (by rw [hm3])
  have R3 : Rep u3.mem F S V2 W1 := hm3 ▸ R2
  have hr3 : hG.SH.Repr u3.mem (off S oSt) [] := hm3 ▸ hr2
  have st3 := st2.trans S3
  have sy3 := s3.trans sy2
  refine WP.seq (WP.mono (wp_sy (updT_ok hG L3 R3 w32 (T.at st3 sy3) (a := src) (len := srcLen)
      (by omega_using [c1, c5, hfs]) (by omega_using [hfs]) (by omega_using [c1, c4, hfs]) x03 x23 x33 x43))
    fun u4 ⟨⟨L4, S4, R4, hr4⟩, s4⟩ => ?_)
  have st4 := st3.trans S4
  have sy4 := s4.trans sy3
  have hR4 := hr4 [] hr3 (by rw [x13]; rfl)
  obtain ⟨V4, R4, hV4, hV4'⟩ := Rep.ex R4
  -- The counter, and `update` with it.
  refine WP.seq (WP.mono (wp_sy (updCtr_ok L4 R4 A1.hsl h17 (by omega_using [hc, hdb, hcD]) []))
    fun u5 ⟨⟨L5, S5, R5, x05, x15, x25, x35, x45⟩, s5⟩ => ?_)
  have hst5 : ∀ i < G.S, u5.mem (off S oSt + BitVec.ofNat 64 i) = u4.mem (off S oSt + BitVec.ofNat 64 i) :=
    fun i hi => by
      show u5.mem (off (off S oSt) i) = u4.mem (off (off S oSt) i)
      rw [off_off, R5.scr _ (by omega_using [hzS, c1, c5, hi]), R4.scr _ (by omega_using [hzS, c1, c5, hi]), ctrV,
          ifn (by omega_using [hzS, c1, c3, hi])]
  have hR5 := hG.repr _ _ _ _ _ hst5 hR4
  have st5 := st4.trans S5
  have sy5 := s5.trans sy4
  refine WP.seq (WP.mono (wp_sy (updT_ok hG L5 R5 w32 (T.at st5 sy5) (a := oCtr) (len := 4)
      (by omega_using [c3, c5]) (by omega_using [hzS, c1, c3]) (by omega_using [c3, c4]) x05 x25 x35 x45))
    fun u6 ⟨⟨L6, S6, R6, hr6⟩, s6⟩ => ?_)
  have st6 := st5.trans S6
  have sy6 := s6.trans sy5
  have hR6 : hG.SH.Repr u6.mem (off S oSt) (srcB V src srcLen ++ Spec.Rsa.i2osp c 4) := repr_congr ?msg
    (hr6 _ hR5 (by rw [x15, List.nil_append, List.length_map, List.length_range]))
  case msg =>
    rw [List.nil_append]
    refine (congrArg (· ++ _) ?_).trans (congrArg (_ ++ ·) ?_)
    · refine List.map_congr_left fun i hi => ?_
      have := List.mem_range.mp hi
      rw [hV2 _ (by simp only [inR_cons, inR_nil, or_false]; omega_using [hfs, this]), hsrc1 i this]
    · refine (List.map_congr_left fun i hi => ?_).trans ((range_map_getD (n := 4) (xs := Spec.Rsa.i2osp c 4)
        (by rw [Proof.Mgf1.i2osp_length])).trans (List.take_of_length_le (by rw [Proof.Mgf1.i2osp_length])))
      have := List.mem_range.mp hi
      rw [ctrV, ifp (by omega_using [this]), Nat.add_sub_cancel_left]
  obtain ⟨V6, R6, hV6, -⟩ := Rep.ex R6
  -- `finalize`.
  refine WP.seq (WP.mono (wp_sy (finA_ok L6 R6 A1.hsl [])) fun u7 ⟨⟨S7, hm7, x07, x17, x27, x37⟩, s7⟩ => ?_)
  have L7 : Lay u7 F S := L6.congr S7.sp S7.wr (by rw [hm7])
  have R7 : Rep u7.mem F S V6 W1 := hm7 ▸ R6
  have hR7 : hG.SH.Repr u7.mem (off S oSt) (srcB V src srcLen ++ Spec.Rsa.i2osp c 4) := hm7 ▸ hR6
  have st7 := st6.trans S7
  have sy7 := s7.trans sy6
  refine WP.seq (WP.mono (wp_sy (finT_ok hG L7 R7 w32 (T.at st7 sy7) (o := oDig) (by omega_using [c1, c2, c4])
      x07 x27 x37)) fun u8 ⟨⟨L8, S8, R8, hr8⟩, s8⟩ => ?_)
  have hml : (srcB V src srcLen ++ Spec.Rsa.i2osp c 4).length = srcLen + 4 := by
    rw [List.length_append, srcB, List.length_map, List.length_range, Proof.Mgf1.i2osp_length]
  have hdig := hr8 _ hR7 (by rw [hml]; omega_using [c1, hfs]) (by rw [x17, hml])
  obtain ⟨V8, R8, hV8, hV8'⟩ := Rep.ex R8
  -- Into `dst`.
  refine WP.seq (WP.mono (wp_sy (xorOutT_ok L8 R8 (D := G.D) (dst := dst) (dstLen := dstLen) (done := c * G.D)
    hfd hzD (by omega_using [hzF, hzDF]) w33 A1.hdst A1.hdl h18 hc [])) fun u9 ⟨⟨L9, S9, R9⟩, s9⟩ => ?_)
  -- The next counter.
  refine WP.mono (wp_sy (nextCtrT_ok L9 R9 (D := G.D) h17 h18 A1.hdl w33
      (by omega_using [hc, hzF, hzDF, hdb]) (by omega_using [hdb]) []))
    fun u10 ⟨⟨L10, S10, x10, R10⟩, s10⟩ => ?_
  have hs1 : (c + 1) * G.D = c * G.D + G.D := Nat.succ_mul _ _
  refine ⟨by rw [x10, hs1], ⟨L10, st6.trans (S7.trans (S8.trans (S9.trans S10))), _, _, R10, by simp [upd],
    by simp [upd, hs1], ?_, ?_⟩, s10.trans (s9.trans (s8.trans sy7))⟩
  · intro k hk h1 h2
    simp only [upd, ifn h2, ifn h1]
    exact hW k hk h1 h2
  · intro o ho hmo
    have hold : ∀ x, mOut x → V8 x = V1 x := by
      intro x hx
      have := (mOut_iff x).mp hx
      rw [hV8 _ (by simp only [inR_cons, inR_nil, or_false]; omega_using [hzS, hzF, hzW, c1, c2, c3, c4, this]),
        hV6 _ (by simp only [inR_cons, inR_nil, or_false]; omega_using [hzS, hzW, c1, c2, c3, c4, this]), ctrV,
            ifn (by omega_using [c1, c3, c4, this]),
        hV4 _ (by simp only [inR_cons, inR_nil, or_false]; omega_using [hzS, hzW, c1, c2, c3, c4, this]),
        hV2 _ (by simp only [inR_cons, inR_nil, or_false]; omega_using [hzS, c1, c2, c3, c4, this])]
    have hdg : ∀ j < G.D, V8 (oDig + j) = (Gs.hash (srcB V src srcLen ++ Spec.Rsa.i2osp c 4)).getD j 0 :=
      fun j hj => by
        rw [hV8' _ (by simp only [inR_cons, inR_nil, or_false]; omega_using [hzDF, hj]), hdig j hj, hGh]
    simp only [xorV]
    by_cases hx : dst + c * G.D ≤ o ∧ o < dst + c * G.D + min G.D (dstLen - c * G.D)
    · have hq : (o - dst) / G.D = c :=
        Nat.div_eq_of_lt_le (by omega_using [hx]) (by omega_using [hs1, hx])
      have hr : (o - dst) % G.D = o - (dst + c * G.D) := by
        rw [Nat.mod_eq_sub_mul_div, hq, Nat.mul_comm]; omega_using []
      rw [ifp hx, hold o hmo, hV o ho hmo, mixV, mixV,
        ifn (show ¬ (dst ≤ o ∧ o < dst + min (c * G.D) dstLen) by omega_using [hx]),
        ifp (show dst ≤ o ∧ o < dst + min ((c + 1) * G.D) dstLen by omega_using [hs1, hx]), hdg _ (by omega_using [hx]),
        Proof.Mgf1.mgf1_getD hGv _ (show o - dst < dstLen by omega_using [hx]), hGl, hq, hr]
    · rw [ifn hx, hold o hmo, hV o ho hmo, mixV, mixV]
      by_cases hy : dst ≤ o ∧ o < dst + min (c * G.D) dstLen
      · rw [ifp hy, ifp (by omega_using [hs1, hy])]
      · rw [ifn hy, ifn (by omega_using [hs1, hx, hy])]

/-! ## MGF1 -/

omit hG in
/-- The table's address to its slot. -/
theorem tabArg_ok {sArg : Nat} (hsa : sArg < 32768 ∧ sArg % 8 = 0) {u : State} {F S p : Addr} (L : Lay u F S)
    {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep u.mem F S V W) (T : Tab G f F S p sArg u) :
    WP isa (.block (tabArg sArg sTab)) u fun u' => Lay u' F S ∧ Step F S [] u u' ∧
      Rep u'.mem F S V (upd W 32 p) ∧ u'.gpr .x10 = p := by
  have G' := L.geo
  have R1 : Rep (u.mem.write (off F 256) 8 p) F S V (upd W 32 p) := R.wq G' (k := 32) (by decide) _
  have w256 : InRegions u.wr (F + BitVec.ofNat 64 256) 8 := L.st (d := 256) (by decide)
  have ha : u.mem.read (F + BitVec.ofNat 64 sArg) 8 = p := by simpa [Mem.readW] using (T.mem _ (Frame.refl _ _)).2.2
  refine WP.mono (Q := fun (u' : State) => u'.mem = u.mem.write (off F 256) 8 p ∧ u'.rd = u.rd ∧
      u'.wr = u.wr ∧ u'.sp = u.sp ∧ u'.v = u.v ∧ (∀ r ∈ preserved, r ≠ .x30 → u'.gpr r = u.gpr r) ∧
      u'.gpr .x10 = p) ?_
    fun u' ⟨hm, hrd, hwr, hsp, hv, hcs, h10⟩ => ?_
  · oaep_run [tabArg, sTab, T.rdA, L.sp, ha, w256, BitVec.add_zero, hsa.1, hsa.2]
    oaep_fin
  have R' : Rep u'.mem F S V (upd W 32 p) := by rw [hm]; exact R1
  refine ⟨L.congr hsp hwr ?_, ⟨hrd, hwr, hsp, hcs, fun r _ => by rw [hv], ?_⟩, R', h10⟩
  · rw [show sScr = 8 * 12 from rfl, R'.fr 12 (by decide), R.fr 12 (by decide)]; rfl
  · rw [hm]; exact Frame.write (Frame.refl _ _) (List.mem_cons_self ..) _ (cF F (by decide))

omit hG in
/-- The table's digest length to its slot, and the counter and `done` set
to 0: the loop's invariant for counter 0. -/
theorem tabHead_ok {u : State} {F S p : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) (h10 : u.gpr .x10 = p) (hrd : InRegions (u.rd ++ u.wr) (off p 32) 8)
    (hD : u.mem.readW (off p 32) 64 = BitVec.ofNat 64 G.D) (mk : List Byte) (dst dstLen : Nat) :
    WP isa (.block (tabHead lay sD)) u
      (MgfI u F S V (upd W 33 (BitVec.ofNat 64 G.D)) mk dst dstLen G.D 0) := by
  have G' := L.geo
  have R3 : Rep (((u.mem.write (off F 264) 8 (BitVec.ofNat 64 G.D)).write (off F 136) 8 (0 : BitVec 64)).write
      (off F 144) 8 (0 : BitVec 64)) F S V (upd (upd (upd W 33 (BitVec.ofNat 64 G.D)) 17 0) 18 0) :=
    ((R.wq G' (k := 33) (by decide) _).wq G' (k := 17) (by decide) 0).wq G' (k := 18) (by decide) 0
  have w264 : InRegions u.wr (F + BitVec.ofNat 64 264) 8 := L.st (d := 264) (by decide)
  have w136 : InRegions u.wr (F + BitVec.ofNat 64 136) 8 := L.st (d := 136) (by decide)
  have w144 : InRegions u.wr (F + BitVec.ofNat 64 144) 8 := L.st (d := 144) (by decide)
  have hD' : u.mem.read (p + BitVec.ofNat 64 32) 8 = BitVec.ofNat 64 G.D := by simpa [Mem.readW] using hD
  refine WP.mono (Q := fun (v : State) => v.mem = ((u.mem.write (off F 264) 8 (BitVec.ofNat 64 G.D)).write
      (off F 136) 8 (0 : BitVec 64)).write (off F 144) 8 (0 : BitVec 64) ∧ v.rd = u.rd ∧ v.wr = u.wr ∧
      v.sp = u.sp ∧ v.v = u.v ∧ (∀ r ∈ preserved, r ≠ .x30 → v.gpr r = u.gpr r)) ?_
    fun v ⟨hm, hrd', hwr, hsp, hv, hcs⟩ => ?_
  · oaep_run [tabHead, lay, sD, sCtr, sDone, h10, hrd, hD', w264, w136, w144, L.sp, BitVec.add_zero]
    oaep_fin
  have R' : Rep v.mem F S V (upd (upd (upd W 33 (BitVec.ofNat 64 G.D)) 17 0) 18 0) := by rw [hm]; exact R3
  refine ⟨L.congr hsp hwr ?_, ⟨hrd', hwr, hsp, hcs, fun r _ => by rw [hv], ?_⟩, _, _, R', by simp [upd],
    by simp [upd], fun k _ h1 h2 => by simp only [upd, ifn h2, ifn h1],
    fun o _ _ => by simp only [mixV, Nat.zero_mul, Nat.zero_min, Nat.add_zero]; rw [ifn (by omega_using [])]⟩
  · rw [show sScr = 8 * 12 from rfl, R'.fr 12 (by decide), R.fr 12 (by decide)]; rfl
  · rw [hm]
    exact Frame.write (Frame.write (Frame.write (Frame.refl _ _) (List.mem_cons_self ..) _ (cF F (by decide)))
      (List.mem_cons_self ..) _ (cF F (by decide))) (List.mem_cons_self ..) _ (cF F (by decide))

include hG in
/-- `dst ⊕= MGF1(src, dstLen)`, with the hash function of the table at
`[sp + sArg]`. -/
theorem mgfXorT_ok {Gs : Spec.Mgf1.Hash} (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = G.D)
    (hGv : Proof.Mgf1.Valid Gs) {sArg : Nat} (hsa : sArg < 32768 ∧ sArg % 8 = 0) {u : State} {F S p : Addr}
    (T : Tab G f F S p sArg u) (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep u.mem F S V W)
    {src srcLen dst dstLen : Nat} (hf : MFit src srcLen dst dstLen) (A : MArgs W S src srcLen dst dstLen) :
    WP isa (Impl.RsaOaep.AArch64.Mgf1.Table.mgfXor lay sArg sTab sD f) u fun u' => Lay u' F S ∧ Step F S [] u u' ∧
      ∃ V' W', Rep u'.mem F S V' W' ∧ (∀ k < nW, k ≠ 17 → k ≠ 18 → k ≠ 32 → k ≠ 33 → W' k = W k) ∧
        ∀ o < oRsa, mOut o → V' o = mixV V (Spec.Mgf1.mgf1 Gs (srcB V src srcLen) dstLen) dst dstLen o := by
  have hpos := hf.pos
  have hD0 := (sizes hG).2.2.2.2
  unfold Impl.RsaOaep.AArch64.Mgf1.Table.mgfXor seqs seqs
  refine WP.seq (WP.mono (wp_sy (tabArg_ok (G := G) hsa L R T)) fun u1 ⟨⟨L1, S1, R1, x10⟩, s1⟩ => ?_)
  have hD := (T.mem _ S1.frame).2.1
  refine WP.seq (WP.mono (wp_sy (tabHead_ok (G := G) L1 R1 x10
      (by rw [S1.rd, S1.wr]; exact T.rdD) hD (Spec.Mgf1.mgf1 Gs (srcB V src srcLen) dstLen) dst dstLen))
    fun v ⟨I0, s0⟩ => ?_)
  have I0' : MgfI u F S V (upd (upd W 32 p) 33 (BitVec.ofNat 64 G.D)) (Spec.Mgf1.mgf1 Gs (srcB V src srcLen) dstLen)
      dst dstLen G.D 0 v := ⟨I0.L, S1.trans I0.st, I0.rep⟩
  have A' : MArgs (upd (upd W 32 p) 33 (BitVec.ofNat 64 G.D)) S src srcLen dst dstLen :=
    A.of_eq fun k h1 h2 => by simp only [upd]; rw [ifn (by omega), ifn (by omega)]
  refine WP.loop (M := isa) (fun n w => ∃ c, n = dstLen - c * G.D ∧ c * G.D < dstLen ∧
      MgfI u F S V (upd (upd W 32 p) 33 (BitVec.ofNat 64 G.D)) (Spec.Mgf1.mgf1 Gs (srcB V src srcLen) dstLen) dst
        dstLen G.D c w ∧ w.syms = u.syms)
    ?_ (dstLen - 0 * G.D) v ⟨0, rfl, by omega_using [hpos], I0', s0.trans s1⟩
  rintro n w ⟨c, rfl, hc, I, sy⟩
  refine WP.mono (roundT_ok hG hGh hGl hGv T hf A' (by simp [upd]) (by simp [upd]) I sy hc)
    fun w' ⟨hcf, I', sy'⟩ => ?_
  have hs1 : (c + 1) * G.D = c * G.D + G.D := Nat.succ_mul _ _
  by_cases h : (c + 1) * G.D < dstLen
  · refine .inr ⟨by rw [eval_nonzero, hcf, decide_eq_true h], _, ?_, c + 1, rfl, h, I', sy'⟩
    omega_using [hD0, hs1, h]
  · refine .inl ⟨by rw [eval_nonzero, hcf, decide_eq_false h], I'.L, I'.st, ?_⟩
    obtain ⟨V', W', R', _, _, hW', hV'⟩ := I'.rep
    exact ⟨V', W', R', fun k hk h17 h18 h32 h33 => by
      rw [hW' k hk h17 h18]; simp only [upd]; rw [ifn h33, ifn h32],
      fun o ho hco => by rw [hV' o ho hco, Nat.min_eq_right (by omega_using [h])]⟩

end VG.Proof.RsaOaep.AArch64.Table
