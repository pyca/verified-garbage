module

import VerifiedGarbage.Proof.RsaOaep.X86_64.Hash
import VerifiedGarbage.Proof.Mgf1.Bytes
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Good
public import VerifiedGarbage.Impl.RsaOaep.X86_64
public import VerifiedGarbage.Proof.Framework.ICall
public import VerifiedGarbage.Proof.Framework.X86_64.Syms
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# RSAES-OAEP on x86-64: MGF1 with the hash function of a table

`Table.mgfXor lay f` (`Impl/RsaOaep/X86_64/Table.lean`) XORs
`MGF1(src, dstLen)` into `dst` as `mgfXor lay G` does (`mgfXorT_ok`, as
`mgfXor_ok`), for `G` the hash function whose functions' addresses the
table holds (`Tab`): the table's address is in the slot `sTab` (word 35)
and `G`'s digest length in `sD` (word 36), and the table holds the
addresses of `G`'s `init`, `update` and `finalize`, which an indirect call
of `f`'s functions reaches (`TabOK`), in every memory that differs from the
entry state's only where MGF1 may write (its writable regions and the
stack below the frame). So each indirect call (`tcall`) runs as `G`'s call
(`initT_ok`, `updT_ok`, `finT_ok`, from `init_ok`, `upd_ok`, `fin_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86_64.Table

open VG VG.X86_64 VG.Impl.RsaOaep.X86_64 VG.Proof.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64.Table (Fns tcall tabArg tabHead)
open VG.Impl.Mgf1.X86_64 (sp ix at_ step byteLoop seqs initArgs updSrcArgs updCtrArgs finArgs)
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.Bignum (off word off_off)
open VG.Impl.Pbkdf2.Md.X86_64 (Stream)
open VG.Proof.Pbkdf2.Md.X86_64.Calls (StreamOK)

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

/-- The table at `p`, from MGF1's entry state `u` with its frame at `F`, the
word at `F + sArg` its address: readable, and holding `G`'s functions'
addresses and its digest length, and that word `p`, in every memory that
differs from `u`'s only within its writable regions and the 16 bytes below
the frame. -/
structure Tab (G : Stream) (f : Fns) (F p : Addr) (sArg : Nat) (u : State) : Prop where
  ok : TabOK G f u.syms
  rd : ∀ j < 3, InRegions (u.rd ++ u.wr) (off p (8 * j)) 8
  rdD : InRegions (u.rd ++ u.wr) (off p 32) 8
  rdA : InRegions (u.rd ++ u.wr) (off F sArg) 8
  mem : ∀ m, Frame (u.wr ++ [below F 16]) u.mem m → TabMem G u.syms p m ∧
    m.readW (off p 32) 64 = BitVec.ofNat 64 G.D ∧ m.readW (off F sArg) 64 = p

/-- The table at `p`, in the state `t`. -/
structure TabAt (G : Stream) (f : Fns) (p : Addr) (t : State) : Prop where
  ok : TabOK G f t.syms
  rd : ∀ j < 3, InRegions (t.rd ++ t.wr) (off p (8 * j)) 8
  mem : TabMem G t.syms p t.mem

/-- What a state `v` of MGF1 keeps of its entry state `u₀`: memory but within
the writable regions and the 16 bytes below the frame, and the addresses of
statics. -/
structure TJ (u₀ : State) (F : Addr) (v : State) : Prop where
  fr : Frame (u₀.wr ++ [below F 16]) u₀.mem v.mem
  sy : v.syms = u₀.syms

theorem TJ.refl (u₀ : State) (F : Addr) : TJ u₀ F u₀ := ⟨Frame.refl _ _, rfl⟩

theorem TJ.step {u₀ v v' : State} {F : Addr} (J : TJ u₀ F v) (hwr : v.wr = u₀.wr) (hsp : v.gpr .rsp = F)
    (hf : Frame (v.wr ++ [below (v.gpr .rsp) 16]) v.mem v'.mem) (hs : v'.syms = v.syms) : TJ u₀ F v' :=
  ⟨J.fr.trans (by rw [hwr, hsp] at hf; exact hf), hs.trans J.sy⟩

theorem Tab.at {G : Stream} {f : Fns} {F p : Addr} {sArg : Nat} {u₀ v : State} (T : Tab G f F p sArg u₀)
    (J : TJ u₀ F v) (hrd : v.rd = u₀.rd) (hwr : v.wr = u₀.wr) : TabAt G f p v :=
  ⟨by rw [J.sy]; exact T.ok, by rw [hrd, hwr]; exact T.rd, by rw [J.sy]; exact (T.mem _ J.fr).1⟩

/-- `Good`, with the addresses of statics kept. -/
theorem wp_gs {c : Prog isa} (hc : Good c) {s : State} {Q : State → Prop} (h : WP isa c s Q) :
    WP isa c s fun s' => Q s' ∧ Frame (s.wr ++ [below (s.gpr .rsp) 16]) s.mem s'.mem ∧ s'.syms = s.syms :=
  WP.mono_syms (wp_good hc h) fun _ ⟨q, _, _, f⟩ sy => ⟨q, f, sy⟩

/-! ## The calls -/

/-- What the pieces need of the functions an indirect call may reach. -/
def FnsGood (ts : List (String × Prog isa)) : Prop := ∀ q ∈ ts, q.2.allInstrs okI = true ∧ q.2.depth ≤ 1

theorem icalls_good : ∀ {ts : List (String × Prog isa)}, FnsGood ts →
    (Code.icalls (.callr .r11) ts).allInstrs okI = true ∧ (Code.icalls (.callr .r11) ts).depth ≤ 2
  | [], _ => ⟨rfl, by simp [Code.icalls, Code.depth]⟩
  | q :: ts, h => by
    have hq := h q (List.mem_cons_self ..)
    have ih := icalls_good (ts := ts) fun r hr => h r (List.mem_cons_of_mem _ hr)
    refine ⟨?_, ?_⟩
    · simp only [Code.icalls, Code.allInstrs, hq.1, ih.1, Bool.and_true]; rfl
    · simp only [Code.icalls, Code.depth, Nat.max_le]; omega

theorem tcall_good {ts : List (String × Prog isa)} (h : FnsGood ts) (j : Nat) : Good (tcall sTab j ts) := by
  have := icalls_good h
  refine ⟨?_, ?_⟩
  · simp only [tcall, Code.allInstrs, this.1, Bool.and_true]; rfl
  · simp only [tcall, Code.depth, Nat.max_le]; omega

theorem mgfT_good {f : Fns} (hgi : FnsGood f.init) (hgu : FnsGood f.upd) (hgf : FnsGood f.fin) (sArg : Nat) :
    Good (Impl.Mgf1.X86_64.Table.mgfXor lay sArg sTab sD f) := by
  have hi := tcall_good hgi 0; have hu := tcall_good hgu 1; have hf := tcall_good hgf 2
  refine ⟨?_, ?_⟩
  · simp only [Impl.Mgf1.X86_64.Table.mgfXor, Impl.Mgf1.X86_64.Table.round, Impl.Mgf1.X86_64.Table.xorOut, seqs,
      Code.allInstrs, hi.1, hu.1, hf.1, Bool.and_true, Bool.true_and]
    rfl
  · have := hi.2; have := hu.2; have := hf.2
    simp only [Impl.Mgf1.X86_64.Table.mgfXor, Impl.Mgf1.X86_64.Table.round, Impl.Mgf1.X86_64.Table.xorOut, seqs,
      Code.depth, Impl.Mgf1.X86_64.byteLoop, Nat.max_le]
    omega

/-- The indirect call of the table's function `j`, at the address `p`'s word
`j` holds, of `n`. -/
theorem tcall_ok {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep t.mem F S V W) {p : Addr} (hp : W 35 = p) {j : Nat} {n : String} {c : Prog isa}
    {ts : List (String × Prog isa)} (hrd : InRegions (t.rd ++ t.wr) (off p (8 * j)) 8)
    (hw : t.mem.readW (off p (8 * j)) 64 = t.syms n)
    (hf : ts.find? (fun q => t.syms q.1 == t.syms n) = some (n, c)) {Q : State → Prop}
    (h : ∀ t', Keep [.r11] t t' → t'.mem = t.mem → t'.syms = t.syms → WP isa (.call n c) t' Q) :
    WP isa (tcall sTab j ts) t Q := by
  refine WP.seq (WP.mono (WP.keep [.r11] (Q := fun t' => t'.gpr .r11 = t.syms n ∧ t'.mem = t.mem ∧
      t'.syms = t.syms) ?_ rfl) fun t' ⟨⟨h11, hm, hs⟩, k⟩ => ?_)
  · xrun [ea_sp, VG.Proof.RsaOaep.X86_64.ea_at, L.rsp, L.ld (d := sTab) (by decide),
      R.slot (d := sTab) (k := 35) rfl (by decide) hp, hrd, hw,
      setReg_syms]
  · refine WP.icalls_of_call (a := t.syms n) (by simp only [icall, h11]) ?_ (h t' k hm hs)
    show ts.find? (fun q => t'.syms q.1 == t.syms n) = _
    rw [hs]; exact hf

variable {G : Stream} (hG : StreamOK G) {f : Fns}

theorem lay_keep11 {t t' : State} {F S : Addr} (L : Lay t F S) (k : Keep [.r11] t t') (hm : t'.mem = t.mem) :
    Lay t' F S := L.congr (k.gpr (by decide)) k.2.2 (by rw [hm])

theorem cs_keep11 {t t' : State} (k : Keep [.r11] t t') : ∀ r ∈ calleeSaved, t'.gpr r = t.gpr r :=
  fun r hr => k.gpr fun h => by simp only [List.mem_singleton] at h; subst h; exact absurd hr (by decide)

include hG in
theorem initT_ok {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep t.mem F S V W) {p : Addr} (hp : W 35 = p) (T : TabAt G f p t) (hdi : t.gpr .rdi = off S oSt) :
    WP isa (tcall sTab 0 f.init) t fun t' => Lay t' F S ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧
      (∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) ∧
      Rep t'.mem F S (fun o => if inR [(oSt, G.S)] o then t'.mem (off S o) else V o) W ∧
      Frame (regs S [(oSt, G.S)] ++ [retR F]) t.mem t'.mem ∧
      hG.SH.Repr t'.mem (off S oSt) [] :=
  tcall_ok L R hp (T.rd 0 (by decide)) T.mem.1 T.ok.i fun u k hm _ =>
    WP.mono (init_ok hG (lay_keep11 L k hm) (hm ▸ R) ((k.gpr (by decide)).trans hdi))
      fun t' ⟨L', rd', wr', cs', R', F', hr'⟩ => ⟨L', rd'.trans k.2.1, wr'.trans k.2.2,
        fun r hr => (cs' r hr).trans (cs_keep11 k r hr), R', hm ▸ F', hr'⟩

include hG in
theorem updT_ok {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep t.mem F S V W) {p : Addr} (hp : W 35 = p) (T : TabAt G f p t) {a len : Nat} (ha : a + len ≤ oRsa)
    (hda : a + len ≤ oSt ∨ oSt + G.S ≤ a) (hwa : a + len ≤ oW ∨ oW + hG.Wb ≤ a)
    (hdi : t.gpr .rdi = off S oSt) (hdx : t.gpr .rdx = off S a) (hcx : t.gpr .rcx = BitVec.ofNat 64 len)
    (h8 : t.gpr .r8 = off S oW) :
    WP isa (tcall sTab 1 f.upd) t fun t' => Lay t' F S ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧
      (∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) ∧
      Rep t'.mem F S (fun o => if inR [(oSt, G.S), (oW, hG.Wb)] o then t'.mem (off S o) else V o) W ∧
      (∀ m, hG.SH.Repr t.mem (off S oSt) m → t.gpr .rsi = BitVec.ofNat 64 m.length →
        hG.SH.Repr t'.mem (off S oSt) (m ++ (List.range len).map fun i => V (a + i))) :=
  tcall_ok L R hp (T.rd 1 (by decide)) T.mem.2.1 T.ok.u fun u k hm _ =>
    WP.mono (upd_ok hG (lay_keep11 L k hm) (hm ▸ R) ha hda hwa ((k.gpr (by decide)).trans hdi)
        ((k.gpr (by decide)).trans hdx) ((k.gpr (by decide)).trans hcx) ((k.gpr (by decide)).trans h8))
      fun t' ⟨L', rd', wr', cs', R', hr'⟩ => ⟨L', rd'.trans k.2.1, wr'.trans k.2.2,
        fun r hr => (cs' r hr).trans (cs_keep11 k r hr), R', fun m hm' hc =>
          hr' m (hm ▸ hm') ((k.gpr (by decide)).trans hc)⟩

include hG in
theorem finT_ok {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep t.mem F S V W) {p : Addr} (hp : W 35 = p) (T : TabAt G f p t) {o : Nat}
    (ho : o + 64 ≤ oSt ∨ (oSt + 256 ≤ o ∧ o + 64 ≤ oW))
    (hdi : t.gpr .rdi = off S oSt) (hdx : t.gpr .rdx = off S o) (hcx : t.gpr .rcx = off S oW) :
    WP isa (tcall sTab 2 f.fin) t fun t' => Lay t' F S ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧
      (∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) ∧
      Rep t'.mem F S (fun x => if inR [(oSt, G.S), (o, G.F), (oW, hG.Wb)] x then t'.mem (off S x) else V x) W ∧
      (∀ m, hG.SH.Repr t.mem (off S oSt) m → m.length < 2 ^ 64 → t.gpr .rsi = BitVec.ofNat 64 m.length →
        ∀ i < G.D, t'.mem (off S (o + i)) = (hG.SH.H.hash m).getD i 0) :=
  tcall_ok L R hp (T.rd 2 (by decide)) T.mem.2.2 T.ok.f fun u k hm _ =>
    WP.mono (fin_ok hG (lay_keep11 L k hm) (hm ▸ R) ho ((k.gpr (by decide)).trans hdi)
        ((k.gpr (by decide)).trans hdx) ((k.gpr (by decide)).trans hcx))
      fun t' ⟨L', rd', wr', cs', R', hr'⟩ => ⟨L', rd'.trans k.2.1, wr'.trans k.2.2,
        fun r hr => (cs' r hr).trans (cs_keep11 k r hr), R', fun m hm' hl hc =>
          hr' m (hm ▸ hm') hl ((k.gpr (by decide)).trans hc)⟩

/-! ## The digest into `dst` -/

omit hG in
theorem xorOutT_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {dst dstLen done : Nat} (hfit : dst + dstLen ≤ oSt) (hD : 0 < G.D) (hDF : G.D ≤ 64)
    (h36 : W 36 = BitVec.ofNat 64 G.D)
    (he : W 17 = off S dst) (hdb : W 18 = BitVec.ofNat 64 dstLen) (hdn : W 20 = BitVec.ofNat 64 done)
    (hlt : done < dstLen) :
    WP isa (Impl.Mgf1.X86_64.Table.xorOut lay sD) u fun u' => Lay u' F S ∧ Keep [.rcx, .rdi, .rax, .r10, .r8, .rdx] u u' ∧
      Rep u'.mem F S (xorV V oDig (dst + done) (min G.D (dstLen - done))) W := by
  have c1 : oSt = 3072 := rfl
  have c3 : oDig = 3328 := rfl
  have hs := L.slot
  simp only [Bignum.word] at hs
  unfold Impl.Mgf1.X86_64.Table.xorOut seqs seqs seqs
  refine WP.seq (WP.mono (WP.keep [.rcx, .rdi, .rax, .r10, .rdx] (Q := fun v => v.gpr .rcx = off S oDig ∧
      v.gpr .rdi = off S (dst + done) ∧ v.gpr .rax = BitVec.ofNat 64 (dstLen - done) ∧
      v.gpr .r10 = BitVec.ofNat 64 G.D ∧ v.cf = some (decide (dstLen - done < G.D)) ∧ v.mem = u.mem) ?_ rfl)
    fun v ⟨⟨h₁, h₂, h₃, h₄, h₅, hm⟩, hk⟩ => ?_)
  · xrun [Impl.Mgf1.X86_64.Table.xorHead, Impl.Mgf1.X86_64.scr, lay, List.cons_append, List.nil_append, ea_sp,
      L.rsp, L.ld (d := sScr) (by decide), hs, VG.Proof.MlKem.X86_64.sx_ofNat (show oDig < 2 ^ 31 by decide),
      L.ld (d := sDst) (by decide), L.ld (d := sDone) (by decide), L.ld (d := sDstLen) (by decide),
      L.ld (d := sD) (by decide), R.slot (d := sD) (k := 36) rfl (by decide) h36,
      R.slot (d := sDst) (k := 17) rfl (by decide) he, R.slot (d := sDstLen) (k := 18) rfl (by decide) hdb,
      R.slot (d := sDone) (k := 20) rfl (by decide) hdn,
      VG.Offset.ofNat_sub_ofNat (show done ≤ dstLen by omega_using [hlt]), off_plus]
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hfit, c1]),
      Nat.mod_eq_of_lt (by omega_using [hDF])]
  have Lv : Lay v F S := L.congr (hk.gpr (by decide)) hk.2.2 (by rw [hm])
  have Rv : Rep v.mem F S V W := hm ▸ R
  have hmin : 0 < min G.D (dstLen - done) := by omega_using [hD, hlt]
  refine WP.seq (WP.mono (Q := fun (w : State) => Keep [.r10] v w ∧ w.mem = v.mem ∧
      w.gpr .r10 = BitVec.ofNat 64 (min G.D (dstLen - done))) ?_ fun w ⟨kw, hmw, h10⟩ => ?_)
  · refine WP.ite (M := isa) _ (show isa.eval .b v = _ from h₅) (fun hb => ?_) (fun hb => ?_)
    · rw [decide_eq_true_eq] at hb
      refine WP.mono (WP.keep [.r10] (Q := fun w => w.mem = v.mem ∧ w.gpr .r10 = BitVec.ofNat 64 (dstLen - done))
        ?_ rfl) fun w ⟨⟨hm', h'⟩, k'⟩ => ⟨k', hm', by rw [h', Nat.min_eq_right (by omega_using [hb])]⟩
      xrun [h₃]
    · rw [decide_eq_false_iff_not] at hb
      refine WP.mono (WP.keep [] (Q := fun w => w = v) ?_ rfl) fun w ⟨hw, _⟩ => ?_
      · xrun
      · subst hw; exact ⟨Keep.refl _ _, rfl, by rw [h₄, Nat.min_eq_left (by omega_using [hb])]⟩
  have Lw : Lay w F S := Lv.congr (kw.gpr (by decide)) kw.2.2 (by rw [hmw])
  have Rw : Rep w.mem F S V W := hmw ▸ Rv
  refine WP.seq (WP.mono (WP.keep [.r8] (Q := fun x => x.gpr .r8 = BitVec.ofNat 64 0 ∧ x.mem = w.mem) ?_ rfl)
    fun x ⟨⟨h8, hmx⟩, kx⟩ => ?_)
  · xrun
  have Lx : Lay x F S := Lw.congr (kx.gpr (by decide)) kx.2.2 (by rw [hmx])
  have Rx : Rep x.mem F S V W := hmx ▸ Rw
  have kvx := kw.trans kx
  refine WP.mono (xor_ok Lx Rx (a := oDig) (b := dst + done) (n := min G.D (dstLen - done))
    (stepR_ok (by omega_using [hDF]) x (show Reg.r10 ∉ [Reg.rax, .rdx, .r8] by decide) (by decide)
      ((kx.gpr (by decide)).trans h10)) hmin (by unfold oRsa; omega_using [hDF, c3])
      (by unfold oRsa; omega_using [hfit, c1, hmin]) (by omega_using [hfit, c1, c3])
    ((kvx.gpr (by decide)).trans h₁) ((kvx.gpr (by decide)).trans h₂) h8)
    fun y ⟨Ly, ky, Ry⟩ => ⟨Ly, ?_, Ry⟩
  exact (hk.trans (kvx.trans ky)).mono (by decide)

/-! ## The next counter -/

omit hG in
theorem nextCtrT_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {c done dstLen : Nat} (hc : W 19 = BitVec.ofNat 64 c)
    (hdn : W 20 = BitVec.ofNat 64 done) (hdb : W 18 = BitVec.ofNat 64 dstLen) (h36 : W 36 = BitVec.ofNat 64 G.D)
    (hd' : done + G.D < 2 ^ 32) (hdb' : dstLen < 2 ^ 32) :
    WP isa (.block (Impl.Mgf1.X86_64.Table.nextCtr lay sD)) u fun u' => Lay u' F S ∧ Keep [.rax] u u' ∧
      u'.cf = some (decide (done + G.D < dstLen)) ∧
      Rep u'.mem F S V (upd (upd W 19 (BitVec.ofNat 64 (c + 1))) 20 (BitVec.ofNat 64 (done + G.D))) := by
  have G' := L.geo
  have R1 := R.wf G' (k := 19) (by decide) (BitVec.ofNat 64 (c + 1))
  have R2 := R1.wf G' (k := 20) (by decide) (BitVec.ofNat 64 (done + G.D))
  rw [show off F (8 * 19) = off F sCtr from rfl] at R1 R2
  rw [show off F (8 * 20) = off F sDone from rfl] at R2
  have h20 : (u.mem.writeW (off F sCtr) (BitVec.ofNat 64 (c + 1))).readW (off F sDone) 64 =
      BitVec.ofNat 64 done := by
    have := R1.fr 20 (by decide); simp only [upd, Nat.reduceEqDiff, ite_false] at this; rw [← hdn, ← this]; rfl
  have h36' : (u.mem.writeW (off F sCtr) (BitVec.ofNat 64 (c + 1))).readW (off F sD) 64 =
      BitVec.ofNat 64 G.D := by
    have := R1.fr 36 (by decide); simp only [upd, Nat.reduceEqDiff, ite_false] at this; rw [← h36, ← this]; rfl
  have h18 : ((u.mem.writeW (off F sCtr) (BitVec.ofNat 64 (c + 1))).writeW (off F sDone)
      (BitVec.ofNat 64 (done + G.D))).readW (off F sDstLen) 64 = BitVec.ofNat 64 dstLen := by
    have := R2.fr 18 (by decide); simp only [upd, Nat.reduceEqDiff, ite_false] at this; rw [← hdb, ← this]; rfl
  refine WP.mono (WP.keep [.rax] (Q := fun u' => u'.cf = some (decide (done + G.D < dstLen)) ∧ u'.mem =
      (u.mem.writeW (off F sCtr) (BitVec.ofNat 64 (c + 1))).writeW (off F sDone) (BitVec.ofNat 64 (done + G.D)))
      ?_ rfl) fun u' ⟨⟨hcf, hm⟩, hk⟩ => ⟨?_, hk, hcf, hm ▸ R2⟩
  · xrun [Impl.Mgf1.X86_64.Table.nextCtr, lay, ea_sp, L.rsp, L.ld (d := sCtr) (by decide),
      L.ld (d := sDone) (by decide), L.ld (d := sD) (by decide),
      L.ld (d := sDstLen) (by decide), L.st (d := sCtr) (by decide), L.st (d := sDone) (by decide),
      R.slot (d := sCtr) (k := 19) rfl (by decide) hc, h20, h36', h18,
      ofNat_add_lit, BitVec.ofNat_add_ofNat]
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hd']),
      Nat.mod_eq_of_lt (by omega_using [hdb'])]
  · refine L.congr (hk.gpr (by decide)) hk.2.2 ?_
    have h1 := R2.fr 14 (by decide)
    rw [← hm] at h1
    rw [slot_eq sScr 14 rfl, slot_eq sScr 14 rfl, h1, R.fr 14 (by decide)]
    simp [upd]

/-! ## One counter -/

include hG in
theorem roundT_ok (hgi : FnsGood f.init) (hgu : FnsGood f.upd) (hgf : FnsGood f.fin)
    {Gs : Spec.Mgf1.Hash} (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = G.D)
    (hGv : Proof.Mgf1.Valid Gs) {u₀ : State} {F S p : Addr} {sArg : Nat} (T : Tab G f F p sArg u₀) {V : Nat → Byte}
    {W : Nat → BitVec 64} {src srcLen dst dstLen c : Nat} (hf : MFit src srcLen dst dstLen)
    (A : MArgs W S src srcLen dst dstLen) (h35 : W 35 = p) (h36 : W 36 = BitVec.ofNat 64 G.D)
    {v : State} (I : MgfI u₀ F S V W (Spec.Mgf1.mgf1 Gs (srcB V src srcLen) dstLen) dst dstLen G.D c v)
    (J : TJ u₀ F v) (hc : c * G.D < dstLen) :
    WP isa (Impl.Mgf1.X86_64.Table.round lay sTab sD f) v fun v' => v'.cf = some (decide ((c + 1) * G.D < dstLen)) ∧
      MgfI u₀ F S V W (Spec.Mgf1.mgf1 Gs (srcB V src srcLen) dstLen) dst dstLen G.D (c + 1) v' ∧ TJ u₀ F v' := by
  obtain ⟨hzS, hzF, hzW, hzDF, hzD⟩ := sizes hG
  have c1 : oSt = 3072 := rfl
  have c2 : oDig = 3328 := rfl
  have c3 : oCtr = 3456 := rfl
  have c4 : oW = 4096 := rfl
  have c5 : oRsa = 8192 := rfl
  have hfs := hf.fs
  have hfd := hf.fd
  have hsep := hf.sep
  have hdb := hf.dstB
  have hcD : c ≤ c * G.D := Nat.le_mul_of_pos_right c hzD
  obtain ⟨V1, W1, R1, h19, h20, hW, hV⟩ := I.rep
  have A1 : MArgs W1 S src srcLen dst dstLen := A.of_eq fun k h1 h2 => hW k (by unfold nW frameBytes; omega_using [h2])
    (by omega_using [h2]) (by omega_using [h2])
  have w35 : W1 35 = p := (hW 35 (by decide) (by decide) (by decide)).trans h35
  have w36 : W1 36 = BitVec.ofNat 64 G.D := (hW 36 (by decide) (by decide) (by decide)).trans h36
  have hsrc1 : ∀ i < srcLen, V1 (src + i) = V (src + i) := fun i hi => by
    rw [hV _ (by omega_using [c1, c5, hfs, hi]) ((mOut_iff _).mpr (by omega_using [hfs, hi])), mixV,
      ifn (by omega_using [hsep, hi])]
  unfold Impl.Mgf1.X86_64.Table.round seqs seqs seqs seqs seqs seqs seqs seqs seqs seqs
  -- `init`.
  refine WP.seq (WP.mono (wp_gs (block_good _ rfl) (scr_ok I.L (d := .rdi) (by decide) (o := oSt) (by decide)))
    fun u1 ⟨⟨hdi1, hm1, k1⟩, f1, s1⟩ => ?_)
  have L1 : Lay u1 F S := I.L.congr (k1.gpr (by decide)) k1.2.2 (by rw [hm1])
  have R1' : Rep u1.mem F S V1 W1 := hm1 ▸ R1
  have rd1 : u1.rd = u₀.rd := k1.2.1.trans I.rd
  have wr1 : u1.wr = u₀.wr := k1.2.2.trans I.wr
  have J1 := J.step I.wr I.L.rsp f1 s1
  refine WP.seq (WP.mono (wp_gs (tcall_good hgi 0) (initT_ok hG L1 R1' w35 (T.at J1 rd1 wr1) hdi1))
    fun u2 ⟨⟨L2, rd2, wr2, cs2, R2, _, hr2⟩, f2, s2⟩ => ?_)
  have J2 := J1.step wr1 L1.rsp f2 s2
  obtain ⟨V2, R2, hV2, -⟩ := Rep.ex R2
  -- `update` with `src`.
  refine WP.seq (WP.mono (wp_gs (block_good _ rfl) (updSrc_ok L2 R2 A1))
    fun u3 ⟨⟨hdi3, hsi3, hdx3, hcx3, h83, hm3, k3⟩, f3, s3⟩ => ?_)
  have L3 : Lay u3 F S := L2.congr (k3.gpr (by decide)) k3.2.2 (by rw [hm3])
  have R3 : Rep u3.mem F S V2 W1 := hm3 ▸ R2
  have hr3 : hG.SH.Repr u3.mem (off S oSt) [] := hm3 ▸ hr2
  have rd3 : u3.rd = u₀.rd := k3.2.1.trans (rd2.trans rd1)
  have wr3 : u3.wr = u₀.wr := k3.2.2.trans (wr2.trans wr1)
  have J3 := J2.step (wr2.trans wr1) L2.rsp f3 s3
  refine WP.seq (WP.mono (wp_gs (tcall_good hgu 1) (updT_ok hG L3 R3 w35 (T.at J3 rd3 wr3) (a := src)
      (len := srcLen) (by omega_using [c1, c5, hfs]) (by omega_using [hfs]) (by omega_using [c1, c4, hfs])
    hdi3 hdx3 hcx3 h83)) fun u4 ⟨⟨L4, rd4, wr4, cs4, R4, hr4⟩, f4, s4⟩ => ?_)
  have J4 := J3.step wr3 L3.rsp f4 s4
  have hR4 := hr4 [] hr3 (by rw [hsi3]; rfl)
  obtain ⟨V4, R4, hV4, hV4'⟩ := Rep.ex R4
  -- The counter, and `update` with it.
  refine WP.seq (WP.mono (wp_gs (block_good _ rfl) (updCtr_ok L4 R4 A1.hsl h19 (by omega_using [hc, hdb, hcD])))
    fun u5 ⟨⟨L5, hdi5, hsi5, hdx5, hcx5, h85, k5, R5⟩, f5, s5⟩ => ?_)
  have hst5 : ∀ i < G.S, u5.mem (off S oSt + BitVec.ofNat 64 i) = u4.mem (off S oSt + BitVec.ofNat 64 i) :=
    fun i hi => by
      rw [off_plus, R5.scr _ (by omega_using [hzS, c1, c5, hi]), R4.scr _ (by omega_using [hzS, c1, c5, hi]), ctrV,
          ifn (by omega_using [hzS, c1, c3, hi])]
  have hR5 := hG.repr _ _ _ _ _ hst5 hR4
  have rd5 : u5.rd = u₀.rd := k5.2.1.trans (rd4.trans rd3)
  have wr5 : u5.wr = u₀.wr := k5.2.2.trans (wr4.trans wr3)
  have J5 := J4.step (wr4.trans wr3) L4.rsp f5 s5
  refine WP.seq (WP.mono (wp_gs (tcall_good hgu 1) (updT_ok hG L5 R5 w35 (T.at J5 rd5 wr5) (a := oCtr) (len := 4)
      (by omega_using [c3, c5]) (by omega_using [hzS, c1, c3]) (by omega_using [c3, c4])
    hdi5 hdx5 hcx5 h85)) fun u6 ⟨⟨L6, rd6, wr6, cs6, R6, hr6⟩, f6, s6⟩ => ?_)
  have J6 := J5.step wr5 L5.rsp f6 s6
  have hR6 : hG.SH.Repr u6.mem (off S oSt) (srcB V src srcLen ++ Spec.Rsa.i2osp c 4) := repr_congr ?msg
    (hr6 _ hR5 (by rw [hsi5, List.nil_append, List.length_map, List.length_range]))
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
  refine WP.seq (WP.mono (wp_gs (block_good _ rfl) (finA_ok L6 R6 A1.hsl))
    fun u7 ⟨⟨hdi7, hsi7, hdx7, hcx7, hm7, k7⟩, f7, s7⟩ => ?_)
  have L7 : Lay u7 F S := L6.congr (k7.gpr (by decide)) k7.2.2 (by rw [hm7])
  have R7 : Rep u7.mem F S V6 W1 := hm7 ▸ R6
  have hR7 : hG.SH.Repr u7.mem (off S oSt) (srcB V src srcLen ++ Spec.Rsa.i2osp c 4) := hm7 ▸ hR6
  have rd7 : u7.rd = u₀.rd := k7.2.1.trans (rd6.trans rd5)
  have wr7 : u7.wr = u₀.wr := k7.2.2.trans (wr6.trans wr5)
  have J7 := J6.step (wr6.trans wr5) L6.rsp f7 s7
  refine WP.seq (WP.mono (wp_gs (tcall_good hgf 2) (finT_ok hG L7 R7 w35 (T.at J7 rd7 wr7) (o := oDig)
      (by omega_using [c1, c2, c4]) hdi7 hdx7 hcx7)) fun u8 ⟨⟨L8, rd8, wr8, cs8, R8, hr8⟩, f8, s8⟩ => ?_)
  have J8 := J7.step wr7 L7.rsp f8 s8
  have hml : (srcB V src srcLen ++ Spec.Rsa.i2osp c 4).length = srcLen + 4 := by
    rw [List.length_append, srcB, List.length_map, List.length_range, Proof.Mgf1.i2osp_length]
  have hdig := hr8 _ hR7 (by rw [hml]; omega_using [c1, hfs]) (by rw [hsi7, hml])
  obtain ⟨V8, R8, hV8, hV8'⟩ := Rep.ex R8
  -- Into `dst`.
  have hlt : c * G.D < dstLen := hc
  have wr8 : u8.wr = u₀.wr := wr8.trans wr7
  refine WP.seq (WP.mono (wp_gs ⟨rfl, by simp [Impl.Mgf1.X86_64.Table.xorOut, seqs, Code.depth,
      Impl.Mgf1.X86_64.byteLoop]⟩ (xorOutT_ok (G := G) L8 R8 (dst := dst) (dstLen := dstLen) (done := c * G.D)
      hfd hzD (by omega_using [hzF, hzDF]) w36 A1.hdst A1.hdl h20 hlt))
    fun u9 ⟨⟨L9, k9, R9⟩, f9, s9⟩ => ?_)
  have J9 := J8.step wr8 L8.rsp f9 s9
  -- The next counter.
  refine WP.mono (wp_gs (block_good _ rfl) (nextCtrT_ok (G := G) L9 R9 h19 h20 A1.hdl w36
      (by omega_using [hzF, hzDF, hdb, hlt]) (by omega_using [hdb])))
    fun u10 ⟨⟨L10, k10, cf10, R10⟩, f10, s10⟩ => ?_
  have J10 := J9.step (k9.2.2.trans wr8) L9.rsp f10 s10
  have hs1 : (c + 1) * G.D = c * G.D + G.D := Nat.succ_mul _ _
  refine ⟨by rw [cf10, hs1], ⟨L10, ?_, ?_, ?_, _, _, R10, by simp [upd], by simp [upd, hs1], ?_, ?_⟩, J10⟩
  · rw [k10.2.1, k9.2.1, rd8, rd7]
  · rw [k10.2.2, k9.2.2, wr8]
  · intro r hr
    rw [keep_cs' k10 (cs_disj _ (by decide)) r hr, keep_cs' k9 (cs_disj _ (by decide)) r hr, cs8 r hr,
      keep_cs' k7 (cs_disj _ (by decide)) r hr, cs6 r hr, keep_cs' k5 (cs_disj _ (by decide)) r hr, cs4 r hr,
      keep_cs' k3 (cs_disj _ (by decide)) r hr, cs2 r hr, keep_cs' k1 (cs_disj _ (by decide)) r hr, I.cs r hr]
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
theorem tabArg_ok {sArg : Nat} {u : State} {F S p : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) (T : Tab G f F p sArg u) :
    WP isa (.block (tabArg sArg sTab)) u fun u' => Keep [.rax] u u' ∧ Lay u' F S ∧ Rep u'.mem F S V (upd W 35 p) ∧
      u'.syms = u.syms := by
  have G' := L.geo
  have R1 := R.wf G' (k := 35) (by decide) p
  rw [show off F (8 * 35) = off F sTab from rfl] at R1
  refine WP.mono (WP.keep [.rax] (Q := fun u' => u'.mem = u.mem.writeW (off F sTab) p ∧ u'.syms = u.syms) ?_ rfl)
    fun u' ⟨⟨hm, hs⟩, k⟩ => ⟨k, ?_, hm ▸ R1, hs⟩
  · xrun [tabArg, ea_sp, L.rsp, T.rdA, (T.mem _ (Frame.refl _ _)).2.2, L.st (d := sTab) (by decide), setReg_syms]
  · refine L.congr (k.gpr (by decide)) k.2.2 ?_
    have h1 := R1.fr 14 (by decide)
    rw [← hm] at h1
    rw [slot_eq sScr 14 rfl, slot_eq sScr 14 rfl, h1, R.fr 14 (by decide)]
    simp [upd]

/-- `MgfI` from another state with the same regions and callee-saved registers. -/
theorem mgfI_rebase {u₀ u₁ v : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64} {mk : List Byte}
    {dst dstLen D c : Nat} (I : MgfI u₁ F S V W mk dst dstLen D c v) (hrd : u₁.rd = u₀.rd) (hwr : u₁.wr = u₀.wr)
    (hcs : ∀ r ∈ calleeSaved, u₁.gpr r = u₀.gpr r) : MgfI u₀ F S V W mk dst dstLen D c v :=
  ⟨I.L, I.rd.trans hrd, I.wr.trans hwr, fun r hr => (I.cs r hr).trans (hcs r hr), I.rep⟩

omit hG in
/-- The table's digest length to its slot, and the counter and `done` set
to 0: the loop's invariant for counter 0. -/
theorem tabHead_ok {u : State} {F S p : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) (h35 : W 35 = p) (hrd : InRegions (u.rd ++ u.wr) (off p 32) 8)
    (hD : u.mem.readW (off p 32) 64 = BitVec.ofNat 64 G.D) (mk : List Byte) (dst dstLen : Nat) :
    WP isa (.block (tabHead lay sTab sD)) u fun v =>
      MgfI u F S V (upd W 36 (BitVec.ofNat 64 G.D)) mk dst dstLen G.D 0 v ∧ v.syms = u.syms := by
  have G' := L.geo
  have R1 := R.wf G' (k := 36) (by decide) (BitVec.ofNat 64 G.D)
  rw [show off F (8 * 36) = off F sD from rfl] at R1
  rw [show tabHead lay sTab sD = [.mov .rax (.mem (sp sTab)), .mov .rax (.mem (at_ .rax 32)), .store (sp sD) .rax] ++
    [.mov32 .rax (.imm 0), .store (sp lay.sCtr) .rax, .store (sp lay.sDone) .rax] from rfl, WP.block_append_iff]
  refine WP.mono (WP.keep [.rax] (Q := fun u' => u'.mem = u.mem.writeW (off F sD) (BitVec.ofNat 64 G.D) ∧
      u'.syms = u.syms) ?_ rfl) fun u1 ⟨⟨hm, hs⟩, k⟩ => ?_
  · xrun [ea_sp, VG.Proof.RsaOaep.X86_64.ea_at, L.rsp, L.ld (d := sTab) (by decide),
      R.slot (d := sTab) (k := 35) rfl (by decide) h35, hrd, hD, L.st (d := sD) (by decide), setReg_syms]
  have R1' : Rep u1.mem F S V (upd W 36 (BitVec.ofNat 64 G.D)) := hm ▸ R1
  have L1 : Lay u1 F S := L.congr (k.gpr (by decide)) k.2.2 (by
    rw [slot_eq sScr 14 rfl, slot_eq sScr 14 rfl, R1'.fr 14 (by decide), R.fr 14 (by decide)]; simp [upd])
  refine WP.mono_syms (mgfHead_ok (G := G) L1 R1' mk dst dstLen) fun v I hs' => ⟨mgfI_rebase I k.2.1 k.2.2
    (keep_cs' k (cs_disj _ (by decide))), hs'.trans hs⟩

include hG in
/-- `dst ⊕= MGF1(src, dstLen)`, with the hash function of the table at
`[rsp + sArg]`. -/
theorem mgfXorT_ok (hgi : FnsGood f.init) (hgu : FnsGood f.upd) (hgf : FnsGood f.fin)
    {Gs : Spec.Mgf1.Hash} (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = G.D)
    (hGv : Proof.Mgf1.Valid Gs) {sArg : Nat} {u : State} {F S p : Addr} (T : Tab G f F p sArg u)
    (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep u.mem F S V W) {src srcLen dst dstLen : Nat}
    (hf : MFit src srcLen dst dstLen) (A : MArgs W S src srcLen dst dstLen) :
    WP isa (Impl.Mgf1.X86_64.Table.mgfXor lay sArg sTab sD f) u fun u' => Lay u' F S ∧ u'.rd = u.rd ∧
      u'.wr = u.wr ∧ (∀ r ∈ calleeSaved, u'.gpr r = u.gpr r) ∧
      ∃ V' W', Rep u'.mem F S V' W' ∧ (∀ k < nW, k ≠ 19 → k ≠ 20 → k ≠ 35 → k ≠ 36 → W' k = W k) ∧
        ∀ o < oRsa, mOut o → V' o = mixV V (Spec.Mgf1.mgf1 Gs (srcB V src srcLen) dstLen) dst dstLen o := by
  have hpos := hf.pos
  unfold Impl.Mgf1.X86_64.Table.mgfXor seqs seqs
  refine WP.seq (WP.mono (wp_gs (block_good _ rfl) (tabArg_ok (G := G) L R T)) fun u1 ⟨⟨k1, L1, R1, _⟩, f1, s1⟩ => ?_)
  have J1 := (TJ.refl u F).step rfl L.rsp f1 s1
  have hrd1 : u1.rd = u.rd := k1.2.1
  have hwr1 : u1.wr = u.wr := k1.2.2
  have hD := (T.mem _ J1.fr).2.1
  refine WP.seq (WP.mono (wp_gs (block_good _ rfl) (tabHead_ok (G := G) L1 R1 (by simp [upd])
      (by rw [hrd1, hwr1]; exact T.rdD) hD (Spec.Mgf1.mgf1 Gs (srcB V src srcLen) dstLen) dst dstLen))
    fun v ⟨⟨I0, _⟩, f0, s0⟩ => ?_)
  have J0 := J1.step hwr1 L1.rsp f0 s0
  have I0' := mgfI_rebase I0 hrd1 hwr1 (keep_cs' k1 (cs_disj _ (by decide)))
  have A' : MArgs (upd (upd W 35 p) 36 (BitVec.ofNat 64 G.D)) S src srcLen dst dstLen :=
    A.of_eq fun k h1 h2 => by simp only [upd]; rw [ifn (by omega), ifn (by omega)]
  refine WP.loop (M := isa) (fun n w => ∃ c, n = dstLen - c * G.D ∧ c * G.D < dstLen ∧
      MgfI u F S V (upd (upd W 35 p) 36 (BitVec.ofNat 64 G.D)) (Spec.Mgf1.mgf1 Gs (srcB V src srcLen) dstLen) dst
        dstLen G.D c w ∧ TJ u F w)
    ?_ (dstLen - 0 * G.D) v ⟨0, rfl, by omega_using [hpos], I0', J0⟩
  rintro n w ⟨c, rfl, hc, I, J⟩
  refine WP.mono (roundT_ok hG hgi hgu hgf hGh hGl hGv T hf A' (by simp [upd]) (by simp [upd]) I J hc)
    fun w' ⟨hcf, I', J'⟩ => ?_
  have hD0 := (sizes hG).2.2.2.2
  have hs1 : (c + 1) * G.D = c * G.D + G.D := Nat.succ_mul _ _
  by_cases h : (c + 1) * G.D < dstLen
  · refine .inr ⟨by simp only [eval, hcf, h, decide_true], _, ?_, c + 1, rfl, h, I', J'⟩
    omega_using [hD0, hs1, h]
  · refine .inl ⟨by simp only [eval, hcf, h, decide_false], I'.L, I'.rd, I'.wr, I'.cs, ?_⟩
    obtain ⟨V', W', R', _, _, hW', hV'⟩ := I'.rep
    exact ⟨V', W', R', fun k hk h19 h20 h35 h36 => by
      rw [hW' k hk h19 h20]; simp only [upd]; rw [ifn h36, ifn h35],
      fun o ho hco => by rw [hV' o ho hco, Nat.min_eq_right (by omega_using [h])]⟩

end VG.Proof.RsaOaep.X86_64.Table
