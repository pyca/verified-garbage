module

public import VerifiedGarbage.Proof.RsaOaep.X86_64.Loops
public import VerifiedGarbage.Proof.HashFns.X86_64.Calls
public import VerifiedGarbage.Proof.HashFns.Streaming
public import VerifiedGarbage.Proof.Framework.X86_64.Dispatch
import Mathlib.Tactic.Conv
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# RSAES-OAEP on x86-64: calling the streaming hash functions

The streaming `init`, `update` and `finalize` of a hash function
(`Spec.HashFns.Streaming`), passed to the function in a table, called from
the frame on the state at `scratch + oSt`, with the working space at
`scratch + oW` and the digest to `scratch + o`: what each leaves of the
frame and the working space (`Lay`, `Rep`, with the ranges it writes read
again), and what it computes. A register `d` is set to `scratch + o` by
`scr_ok`.

Each call is an indirect call of the address in a slot
(`Impl.Mgf1.X86_64.initF`, …): the address is loaded into `r11`
(`ldFn_ok`), and the call is of the function there, which meets its
contract as `FnMeets` says in the function's entry state `e` (`Fns`), from
a state that keeps what `Here` says of `e` (`initF_ok`, …).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86_64

open VG VG.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64 (sp ix at_ step byteLoop)
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.Bignum (off word off_off)
open VG.Proof.Bignum.X86_64 (Scr)
open VG.Proof.Pbkdf2.Md.X86_64.Calls (After)
open VG.Proof.HashFns.X86_64 (UArgs FArgs init_icall upd_icall fin_icall)
open VG.Proof.HashFns (StreamingOK)
open VG.Impl.Mgf1.X86_64 (ldFn initF updF finF)
open VG.Proof.Dispatch.X86_64 (FlagsOnly)


/-- `scratch + o` into `d`. -/
theorem scr_ok {t : State} {F S : Addr} (L : Lay t F S) {d : Reg} (hd : d ≠ .rsp) {o : Nat} (ho : o < 2 ^ 31) :
    WP isa (.block (scr d o)) t fun t' => t'.gpr d = off S o ∧ t'.mem = t.mem ∧ Keep [d] t t' := by
  refine WP.mono (WP.keep [d] (Q := fun t' => t'.gpr d = off S o ∧ t'.mem = t.mem) ?_ ?_) fun t' ⟨h, k⟩ => ⟨h.1, h.2, k⟩
  · have hl := L.ld (d := sScr) (by decide)
    have hs := L.slot
    simp only [Bignum.word] at hs
    xrun [scr, Impl.Mgf1.X86_64.scr, lay, ea_sp, L.rsp, hl, hs, VG.Proof.MlKem.X86_64.sx_ofNat ho]
  · cases d <;> first | exact absurd rfl hd | rfl

/-- What a call leaves of the frame: `Lay`, and the view of memory with the
ranges `rgs` it may write read again. -/
theorem Lay.after_call {t t' : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep t.mem F S V W) {rgs : List (Nat × Nat)} (hrg : ∀ p ∈ rgs, p.1 + p.2 ≤ oRsa)
    (hF : Frame (regs S rgs ++ [retR F]) t.mem t'.mem) (hsp : t'.gpr .rsp = t.gpr .rsp) (hwr : t'.wr = t.wr) :
    Lay t' F S ∧ Rep t'.mem F S (fun o => if inR rgs o then t'.mem (off S o) else V o) W := by
  have R' := R.frame L.geo hrg hF
  refine ⟨L.congr hsp hwr ?_, R'⟩
  rw [slot_eq sScr 14 rfl, slot_eq sScr 14 rfl, R'.fr 14 (by decide), R.fr 14 (by decide)]

variable {T : Spec.HashFns.Streaming} {Hh : Spec.Mgf1.Hash} (hT : StreamingOK T Hh)

include hT in
theorem sizes : T.S.stateBytes ≤ 256 ∧ T.outBytes ≤ 64 ∧ 8 * T.scratch ≤ 2048 ∧
    T.S.digestBytes ≤ T.outBytes ∧ 0 < T.S.digestBytes :=
  ⟨hT.state, hT.out, hT.scratch, hT.digest, hT.pos⟩

/-- A range of our working space and the 16 bytes below the frame are
apart. -/
theorem Lay.stk {t : State} {F S : Addr} (L : Lay t F S) {o n : Nat} (h : o + n ≤ oRsa) :
    (below (t.gpr .rsp) 16).Disjoint ⟨off S o, n⟩ := by
  rw [L.rsp]; exact L.dRS.sub_right (Offset.sub_base S h)

/-- Two ranges of our working space that do not overlap. -/
theorem sdis (S : Addr) {a n b k : Nat} (h : a + n ≤ b ∨ b + k ≤ a) (ha : a + n ≤ oRsa) (hb : b + k ≤ oRsa) :
    Region.Disjoint ⟨off S a, n⟩ ⟨off S b, k⟩ :=
  Offset.disjoint S h (by unfold oRsa at ha; omega) (by unfold oRsa at hb; omega)

/-- After a call that keeps `rsp` and the callee-saved registers. -/
theorem keep_cs {t t' : State} (h : ∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) : t'.gpr .rsp = t.gpr .rsp :=
  h .rsp (by decide)

/-! ## The functions and the state they are called from -/

export VG.Proof.HashFns.X86_64 (Fns)

/-- What a state `t` of a run from the entry `e`, in the frame `F` with the
working space `S`, keeps of `e` for the calls: `World`; what it may write is
`e`'s own, as are our working space and the 16 bytes below the frame. -/
structure Here (stack : Nat) (e t : State) (F S : Addr) : Prop where
  world : World stack e t
  own : Owned stack e t.wr
  scr : Owned stack e [⟨S, oRsa⟩]
  stk : Owned stack e [below F 16]
  sp16 : 16 ≤ F.toNat

/-- A range of our working space is `e`'s own. -/
theorem Here.scrO {stack : Nat} {e t : State} {F S : Addr} (h : Here stack e t F S) {o n : Nat}
    (ho : o + n ≤ oRsa) : Owned stack e [⟨off S o, n⟩] :=
  h.scr.sub (Offset.sub_base S ho)

/-- After a call, which keeps the regions: `Here` of the state after it. -/
theorem Here.after {stack : Nat} {e t t' : State} {F S : Addr} (h : Here stack e t F S)
    (hw : World stack e t') (hwr : t'.wr = t.wr) : Here stack e t' F S :=
  ⟨hw, hwr ▸ h.own, h.scr, h.stk, h.sp16⟩

/-- Code that calls nothing keeps `Here`. -/
theorem WP.here {c : Prog isa} (hc : c.noCalls = true) {stack : Nat} {e t : State} {F S : Addr}
    (h : Here stack e t F S) {Q : State → Prop} (hw : WP isa c t Q) :
    WP isa c t fun t' => Q t' ∧ Here stack e t' F S := by
  obtain ⟨tr, t', he, hq⟩ := hw
  obtain ⟨-, hwr, hF⟩ := Exec.regions he hc
  exact ⟨tr, t', he, hq, h.after (h.world.step (Exec.funs he) (Exec.syms he) hF h.own) hwr⟩

theorem toNat_off {S : Addr} {o : Nat} (h : S.toNat + o < 2 ^ 64) : (off S o).toNat = S.toNat + o := by
  simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := o) (by omega), Nat.mod_eq_of_lt h]

theorem Lay.bound {t : State} {F S : Addr} (L : Lay t F S) {o n : Nat} (h : o + n ≤ oRsa) :
    (off S o).toNat + n ≤ 2 ^ 64 := by
  have := L.Sw
  by_cases hlt : S.toNat + o < 2 ^ 64
  · rw [toNat_off hlt]; omega
  · have := (off S o).isLt; omega

/-! ## `init` -/

include hT in
/-- What a call of `init` on the state at `scratch + oSt` passes. -/
theorem init_pass {stack : Nat} {e t : State} {F S : Addr} (hh : Here stack e t F S) (L : Lay t F S) :
    Passes stack 8 e t [] [⟨off S oSt, T.S.stateBytes⟩] := by
  have hz := sizes hT
  have h1 : oSt + T.S.stateBytes ≤ oRsa := by unfold oSt oRsa; omega
  exact ⟨L.cov h1, by decide, (fun _ h => by cases h), hh.scrO h1, by rw [L.rsp]; exact hh.stk⟩

include hT in
theorem init_ok {stack : Nat} {e : State}
    {t : State} (hm : FnMeets abi (fun A n => Spec.HashFns.initContract T A n) 8 stack e (t.gpr .r11))
    {F S : Addr} (hh : Here stack e t F S) (L : Lay t F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep t.mem F S V W) (hdi : t.gpr .rdi = off S oSt) :
    WP isa (.icall 8) t fun t' => Lay t' F S ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧
      (∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) ∧
      Rep t'.mem F S (fun o => if inR [(oSt, T.S.stateBytes)] o then t'.mem (off S o) else V o) W ∧
      Frame (regs S [(oSt, T.S.stateBytes)] ++ [retR F]) t.mem t'.mem ∧ Here stack e t' F S ∧
      T.S.Repr t'.mem (off S oSt) [] := by
  have hz := sizes hT
  have h1 : oSt + T.S.stateBytes ≤ oRsa := by unfold oSt oRsa; omega
  refine init_icall T hm hh.world hdi (init_pass hT hh L) (L.bound h1) (by rw [L.rsp]; exact hh.sp16) (L.stk h1)
    fun t' A hw hr => ?_
  have hF : Frame (regs S [(oSt, T.S.stateBytes)] ++ [retR F]) t.mem t'.mem := by
    have := A.frame; rw [L.rsp] at this; exact this
  obtain ⟨L', R'⟩ := L.after_call R (rgs := [(oSt, T.S.stateBytes)])
    (by simp only [List.mem_singleton]; rintro p rfl; exact h1) hF (keep_cs A.cs) A.wr
  exact ⟨L', A.rd, A.wr, A.cs, R', hF, hh.after hw A.wr, hr⟩

/-! ## `update` -/

include hT in
/-- The arguments of `update` of the state with the `len` bytes at
`scratch + a`. -/
theorem upd_args {stack : Nat} {e t : State} {F S : Addr} (hh : Here stack e t F S) (L : Lay t F S)
    {a len : Nat} (ha : a + len ≤ oRsa)
    (hda : a + len ≤ oSt ∨ oSt + T.S.stateBytes ≤ a) (hwa : a + len ≤ oW ∨ oW + 8 * T.scratch ≤ a)
    (hdi : t.gpr .rdi = off S oSt) (hdx : t.gpr .rdx = off S a) (hcx : t.gpr .rcx = BitVec.ofNat 64 len)
    (h8 : t.gpr .r8 = off S oW) :
    UArgs T t (off S oSt) (off S a) (off S oW) len ∧
      Passes stack 8 e t [⟨off S a, len⟩] [⟨off S oSt, T.S.stateBytes⟩, ⟨off S oW, 8 * T.scratch⟩] := by
  have hz := sizes hT
  have h1 : oSt + T.S.stateBytes ≤ oRsa := by unfold oSt oRsa; omega
  have h2 : oW + 8 * T.scratch ≤ oRsa := by unfold oW oRsa; omega
  have hsw : oSt + T.S.stateBytes ≤ oW := by unfold oSt oW; omega
  have hrd : ∀ r ∈ [(⟨off S a, len⟩ : Region)], ∀ x, r.Contains x 1 →
      InRegions (e.rd ++ e.wr ++ abi.reserved stack e) x 1 := fun r hr x hx => by
    obtain ⟨R₀, hR, hc⟩ := hh.scrO ha r hr x hx
    refine ⟨R₀, ?_, hc⟩
    rcases List.mem_append.mp hR with h | h
    · exact List.mem_append_left _ (List.mem_append_right _ h)
    · exact List.mem_append_right _ h
  exact ⟨{ rdi := hdi, rdx := hdx
           rcx := by rw [hcx, BitVec.toNat_ofNat]; unfold oRsa at ha; omega
           r8 := h8
           st_sc := sdis S (Or.inl hsw) h1 h2
           d_st := sdis S hda ha h1
           d_sc := sdis S hwa ha h2
           stk_st := L.stk h1, stk_d := L.stk ha, stk_sc := L.stk h2
           bst := L.bound h1, bd := L.bound ha, bsc := L.bound h2
           sp := by rw [L.rsp]; exact hh.sp16 },
    ⟨Covers.pair (L.cov h1) (L.cov h2), by decide, hrd, (hh.scrO h1).pair (hh.scrO h2), by rw [L.rsp]; exact hh.stk⟩⟩

include hT in
/-- `update` of the state with the `len` bytes at `scratch + a`, after
`cnt` bytes, from the arguments in `rdi`, `rsi`, `rdx`, `rcx`, `r8`. -/
theorem upd_ok {stack : Nat} {e : State}
    {t : State} (hm : FnMeets abi (fun A n => Spec.HashFns.updateContract T A n) 8 stack e (t.gpr .r11))
    {F S : Addr} (hh : Here stack e t F S) (L : Lay t F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep t.mem F S V W) {a len : Nat} (ha : a + len ≤ oRsa)
    (hda : a + len ≤ oSt ∨ oSt + T.S.stateBytes ≤ a) (hwa : a + len ≤ oW ∨ oW + 8 * T.scratch ≤ a)
    (hdi : t.gpr .rdi = off S oSt) (hdx : t.gpr .rdx = off S a) (hcx : t.gpr .rcx = BitVec.ofNat 64 len)
    (h8 : t.gpr .r8 = off S oW) :
    WP isa (.icall 8) t fun t' => Lay t' F S ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧
      (∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) ∧
      Rep t'.mem F S (fun o => if inR [(oSt, T.S.stateBytes), (oW, 8 * T.scratch)] o then t'.mem (off S o)
        else V o) W ∧ Here stack e t' F S ∧
      (∀ m, T.S.Repr t.mem (off S oSt) m → t.gpr .rsi = BitVec.ofNat 64 m.length →
        T.S.Repr t'.mem (off S oSt) (m ++ (List.range len).map fun i => V (a + i))) := by
  have hz := sizes hT
  have h1 : oSt + T.S.stateBytes ≤ oRsa := by unfold oSt oRsa; omega
  have h2 : oW + 8 * T.scratch ≤ oRsa := by unfold oW oRsa; omega
  obtain ⟨args, pass⟩ := upd_args hT hh L ha hda hwa hdi hdx hcx h8
  refine upd_icall T hm hh.world hT.local_ args pass fun t' A hw hr => ?_
  obtain ⟨L', R'⟩ := L.after_call R (rgs := [(oSt, T.S.stateBytes), (oW, 8 * T.scratch)])
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro p (rfl | rfl) <;> with_reducible assumption)
    (by have := A.frame; rw [L.rsp] at this; exact this) (keep_cs A.cs) A.wr
  refine ⟨L', A.rd, A.wr, A.cs, R', hh.after hw A.wr, fun m hm hc => ?_⟩
  have e : Spec.Sha256.bytesAt t.mem (off S a) len = (List.range len).map fun i => V (a + i) := by
    simp only [Spec.Sha256.bytesAt]
    exact List.map_congr_left fun i hi => by
      rw [off_plus]; exact R.scr _ (by have := List.mem_range.mp hi; omega)
  rw [← e]; exact hr m hm hc

/-! ## `finalize` -/

include hT in
/-- The arguments of `finalize` of the state to `scratch + o`. -/
theorem fin_args {stack : Nat} {e t : State} {F S : Addr} (hh : Here stack e t F S) (L : Lay t F S)
    {o : Nat} (ho : o + 64 ≤ oSt ∨ (oSt + 256 ≤ o ∧ o + 64 ≤ oW))
    (hdi : t.gpr .rdi = off S oSt) (hdx : t.gpr .rdx = off S o) (hcx : t.gpr .rcx = off S oW) :
    FArgs T t (off S oSt) (off S o) (off S oW) ∧
      Passes stack 8 e t [] [⟨off S oSt, T.S.stateBytes⟩, ⟨off S o, T.outBytes⟩, ⟨off S oW, 8 * T.scratch⟩] := by
  have hz := sizes hT
  have h1 : oSt + T.S.stateBytes ≤ oRsa := by unfold oSt oRsa; omega
  have h2 : oW + 8 * T.scratch ≤ oRsa := by unfold oW oRsa; omega
  have h3 : o + T.outBytes ≤ oRsa := by unfold oSt oW oRsa at *; omega
  have hsw : oSt + T.S.stateBytes ≤ oW := by unfold oSt oW; omega
  exact ⟨{ rdi := hdi, rdx := hdx, rcx := hcx
           st_o := sdis S (by unfold oSt oW at *; omega) h1 h3
           st_sc := sdis S (Or.inl hsw) h1 h2
           o_sc := sdis S (by unfold oSt oW at *; omega) h3 h2
           stk_st := L.stk h1, stk_o := L.stk h3, stk_sc := L.stk h2
           bst := L.bound h1, bo := L.bound h3, bsc := L.bound h2
           sp := by rw [L.rsp]; exact hh.sp16 },
    ⟨Covers.cons (L.cov h1) (Covers.pair (L.cov h3) (L.cov h2)), by decide, (fun _ h => by cases h),
      (hh.scrO h1).cons ((hh.scrO h3).pair (hh.scrO h2)), by rw [L.rsp]; exact hh.stk⟩⟩

include hT in
/-- `finalize` of the state to `scratch + o`, from the arguments in `rdi`,
`rsi`, `rdx`, `rcx`. -/
theorem fin_ok {stack : Nat} {e : State}
    {t : State} (hm : FnMeets abi (fun A n => Spec.HashFns.finalizeContract T A n) 8 stack e (t.gpr .r11))
    {F S : Addr} (hh : Here stack e t F S) (L : Lay t F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep t.mem F S V W) {o : Nat} (ho : o + 64 ≤ oSt ∨ (oSt + 256 ≤ o ∧ o + 64 ≤ oW))
    (hdi : t.gpr .rdi = off S oSt) (hdx : t.gpr .rdx = off S o) (hcx : t.gpr .rcx = off S oW) :
    WP isa (.icall 8) t fun t' => Lay t' F S ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧
      (∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) ∧
      Rep t'.mem F S (fun x => if inR [(oSt, T.S.stateBytes), (o, T.outBytes), (oW, 8 * T.scratch)] x then
        t'.mem (off S x) else V x) W ∧ Here stack e t' F S ∧
      (∀ m, T.S.Repr t.mem (off S oSt) m → m.length < 2 ^ 64 → t.gpr .rsi = BitVec.ofNat 64 m.length →
        ∀ i < T.S.digestBytes, t'.mem (off S (o + i)) = (T.S.H.hash m).getD i 0) := by
  have hz := sizes hT
  have h1 : oSt + T.S.stateBytes ≤ oRsa := by unfold oSt oRsa; omega
  have h2 : oW + 8 * T.scratch ≤ oRsa := by unfold oW oRsa; omega
  have h3 : o + T.outBytes ≤ oRsa := by unfold oSt oW oRsa at *; omega
  obtain ⟨args, pass⟩ := fin_args hT hh L ho hdi hdx hcx
  refine fin_icall T hm hh.world hT.local_ args pass fun t' A hw hr => ?_
  obtain ⟨L', R'⟩ := L.after_call R (rgs := [(oSt, T.S.stateBytes), (o, T.outBytes), (oW, 8 * T.scratch)])
    (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro p (rfl | rfl | rfl) <;> with_reducible assumption)
    (by have := A.frame; rw [L.rsp] at this; exact this) (keep_cs A.cs) A.wr
  refine ⟨L', A.rd, A.wr, A.cs, R', hh.after hw A.wr, fun m hm hl hc i hi => ?_⟩
  have e := hr m hm hl hc
  rw [← e, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi]
  simp only [Spec.Sha256.bytesAt, List.getElem?_map, List.getElem?_range (show i < T.outBytes by omega),
    Option.map_some, Option.getD_some, off_off]

include hT in
/-- The arguments of `update` of the state with the `len` bytes at `d`,
outside our working space and the stack the call uses. -/
theorem updExt_args {stack : Nat} {e t : State} {F S : Addr} (hh : Here stack e t F S) (L : Lay t F S)
    {d : Addr} {len : Nat} (hlen : len < 2 ^ 64) (hbd : d.toNat + len ≤ 2 ^ 64)
    (hcd : ∀ x, (⟨d, len⟩ : Region).Contains x 1 → InRegions (e.rd ++ e.wr ++ abi.reserved stack e) x 1)
    (hds : Region.Disjoint ⟨d, len⟩ ⟨S, oRsa⟩) (hdk : (below F 16).Disjoint ⟨d, len⟩)
    (hdi : t.gpr .rdi = off S oSt) (hdx : t.gpr .rdx = d) (hcx : t.gpr .rcx = BitVec.ofNat 64 len)
    (h8 : t.gpr .r8 = off S oW) :
    UArgs T t (off S oSt) d (off S oW) len ∧
      Passes stack 8 e t [⟨d, len⟩] [⟨off S oSt, T.S.stateBytes⟩, ⟨off S oW, 8 * T.scratch⟩] := by
  have hz := sizes hT
  have h1 : oSt + T.S.stateBytes ≤ oRsa := by unfold oSt oRsa; omega
  have h2 : oW + 8 * T.scratch ≤ oRsa := by unfold oW oRsa; omega
  have hsw : oSt + T.S.stateBytes ≤ oW := by unfold oSt oW; omega
  exact ⟨{ rdi := hdi, rdx := hdx
           rcx := by rw [hcx, BitVec.toNat_ofNat]; omega
           r8 := h8
           st_sc := sdis S (Or.inl hsw) h1 h2
           d_st := hds.sub_right (Offset.sub_base S h1)
           d_sc := hds.sub_right (Offset.sub_base S h2)
           stk_st := L.stk h1, stk_d := by rw [L.rsp]; exact hdk, stk_sc := L.stk h2
           bst := L.bound h1, bd := hbd, bsc := L.bound h2
           sp := by rw [L.rsp]; exact hh.sp16 },
    ⟨Covers.pair (L.cov h1) (L.cov h2), by decide, fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hcd,
      (hh.scrO h1).pair (hh.scrO h2), by rw [L.rsp]; exact hh.stk⟩⟩

include hT in
/-- `update` of the state with the `len` bytes at `d`, outside our working
space and the stack the call uses, after `cnt` bytes. -/
theorem updExt_ok {stack : Nat} {e : State}
    {t : State} (hm : FnMeets abi (fun A n => Spec.HashFns.updateContract T A n) 8 stack e (t.gpr .r11))
    {F S : Addr} (hh : Here stack e t F S) (L : Lay t F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep t.mem F S V W) {d : Addr} {len : Nat} (hlen : len < 2 ^ 64) (hbd : d.toNat + len ≤ 2 ^ 64)
    (hcd : ∀ x, (⟨d, len⟩ : Region).Contains x 1 → InRegions (e.rd ++ e.wr ++ abi.reserved stack e) x 1)
    (hds : Region.Disjoint ⟨d, len⟩ ⟨S, oRsa⟩) (hdk : (below F 16).Disjoint ⟨d, len⟩)
    (hdi : t.gpr .rdi = off S oSt) (hdx : t.gpr .rdx = d) (hcx : t.gpr .rcx = BitVec.ofNat 64 len)
    (h8 : t.gpr .r8 = off S oW) :
    WP isa (.icall 8) t fun t' => Lay t' F S ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧
      (∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) ∧
      Rep t'.mem F S (fun o => if inR [(oSt, T.S.stateBytes), (oW, 8 * T.scratch)] o then t'.mem (off S o)
        else V o) W ∧
      Frame (regs S [(oSt, T.S.stateBytes), (oW, 8 * T.scratch)] ++ [retR F]) t.mem t'.mem ∧
      Here stack e t' F S ∧
      (∀ m, T.S.Repr t.mem (off S oSt) m → t.gpr .rsi = BitVec.ofNat 64 m.length →
        T.S.Repr t'.mem (off S oSt) (m ++ Spec.Rsa.bytesAt t.mem d len)) := by
  have hz := sizes hT
  have h1 : oSt + T.S.stateBytes ≤ oRsa := by unfold oSt oRsa; omega
  have h2 : oW + 8 * T.scratch ≤ oRsa := by unfold oW oRsa; omega
  obtain ⟨args, pass⟩ := updExt_args hT hh L hlen hbd hcd hds hdk hdi hdx hcx h8
  refine upd_icall T hm hh.world hT.local_ args pass fun t' A hw hr => ?_
  have hF : Frame (regs S [(oSt, T.S.stateBytes), (oW, 8 * T.scratch)] ++ [retR F]) t.mem t'.mem := by
    have := A.frame; rw [L.rsp] at this; exact this
  obtain ⟨L', R'⟩ := L.after_call R (rgs := [(oSt, T.S.stateBytes), (oW, 8 * T.scratch)])
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro p (rfl | rfl) <;> with_reducible assumption)
    hF (keep_cs A.cs) A.wr
  exact ⟨L', A.rd, A.wr, A.cs, R', hF, hh.after hw A.wr, fun m hm hc => hr m hm hc⟩

/-! ## The calls through the slots -/

/-- The address in the slot `8 * j` into `r11`. -/
theorem ldFn_ok {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep t.mem F S V W) {sl j : Nat} (hj : sl = 8 * j) (hjn : j < nW) :
    WP isa (.block (ldFn sl)) t fun t' => t'.gpr .r11 = W j ∧ t'.mem = t.mem ∧ Keep [.r11] t t' := by
  refine WP.mono (WP.keep [.r11] (Q := fun t' => t'.gpr .r11 = W j ∧ t'.mem = t.mem) ?_ rfl)
    fun t' ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩
  have hl : InRegions (t.rd ++ t.wr) (off F sl) 8 := L.ld (by subst hj; unfold nW at hjn; unfold frameBytes at hjn ⊢; omega)
  have hv : t.mem.readW (off F sl) 64 = W j := R.rd j hj hjn
  xrun [ldFn, ea_sp, L.rsp, hl, hv]

theorem calleeSaved_ne_r11 : ∀ r ∈ calleeSaved, r ≠ .r11 := by decide

/-- What a call through a slot's address leaves of the state before the load
of the address. -/
theorem keep_r11 {t t₁ : State} (hk : Keep [.r11] t t₁) :
    t₁.rd = t.rd ∧ t₁.wr = t.wr ∧ ∀ r, r ≠ .r11 → t₁.gpr r = t.gpr r :=
  ⟨hk.2.1, hk.2.2, fun r hr => hk.gpr (by simp only [List.mem_singleton]; exact hr)⟩

theorem Here.keep {stack : Nat} {e t t₁ : State} {F S : Addr} (h : Here stack e t F S) (hm : t₁.mem = t.mem)
    (hk : Keep [.r11] t t₁) (hf : t₁.funs = t.funs) (hs : t₁.syms = t.syms) : Here stack e t₁ F S :=
  h.after (h.world.step (ws := []) hf hs (fun x _ => by rw [hm]) (fun _ h => by cases h)) hk.2.2

variable {sl j : Nat}

include hT in
/-- `init` through the address in the slot `sl`. -/
theorem initF_ok {stack : Nat} {e : State} {fi fu ff : Addr} (hF : Fns stack e T fi fu ff) {t : State}
    {F S : Addr} (hh : Here stack e t F S) (L : Lay t F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep t.mem F S V W) (hj : sl = 8 * j) (hjn : j < nW) (hsk : W j = fi) (hdi : t.gpr .rdi = off S oSt) :
    WP isa (initF sl) t fun t' => Lay t' F S ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧
      (∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) ∧
      Rep t'.mem F S (fun o => if inR [(oSt, T.S.stateBytes)] o then t'.mem (off S o) else V o) W ∧
      Frame (regs S [(oSt, T.S.stateBytes)] ++ [retR F]) t.mem t'.mem ∧ Here stack e t' F S ∧
      T.S.Repr t'.mem (off S oSt) [] := by
  refine WP.seq (WP.of_funs (WP.of_syms (WP.mono (ldFn_ok L R hj hjn) fun t₁ ⟨h11, hm, hk1⟩ hsy hfu => ?_)))
  obtain ⟨rd', wr', g'⟩ := keep_r11 hk1
  refine WP.mono (init_ok hT (t := t₁) (by rw [h11, hsk]; exact hF.init) (hh.keep hm hk1 hfu hsy)
    (L.congr (g' _ (by decide)) wr' (by rw [hm])) (hm ▸ R) (by rw [g' _ (by decide), hdi]))
    fun t' ⟨a, b, c, d, e, f, g, h⟩ => ⟨a, b.trans rd', c.trans wr', fun r hr => (d r hr).trans
      (g' r (calleeSaved_ne_r11 r hr)), e, hm ▸ f, g, h⟩

include hT in
/-- `update` through the address in the slot `sl + 8`, with the `len` bytes
at `scratch + a`. -/
theorem updF_ok {stack : Nat} {e : State} {fi fu ff : Addr} (hF : Fns stack e T fi fu ff) {t : State}
    {F S : Addr} (hh : Here stack e t F S) (L : Lay t F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep t.mem F S V W) (hj : sl = 8 * j) (hjn : j + 1 < nW) (hsk : W (j + 1) = fu) {a len : Nat}
    (ha : a + len ≤ oRsa) (hda : a + len ≤ oSt ∨ oSt + T.S.stateBytes ≤ a)
    (hwa : a + len ≤ oW ∨ oW + 8 * T.scratch ≤ a)
    (hdi : t.gpr .rdi = off S oSt) (hdx : t.gpr .rdx = off S a) (hcx : t.gpr .rcx = BitVec.ofNat 64 len)
    (h8 : t.gpr .r8 = off S oW) :
    WP isa (updF sl) t fun t' => Lay t' F S ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧
      (∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) ∧
      Rep t'.mem F S (fun o => if inR [(oSt, T.S.stateBytes), (oW, 8 * T.scratch)] o then t'.mem (off S o)
        else V o) W ∧ Here stack e t' F S ∧
      (∀ m, T.S.Repr t.mem (off S oSt) m → t.gpr .rsi = BitVec.ofNat 64 m.length →
        T.S.Repr t'.mem (off S oSt) (m ++ (List.range len).map fun i => V (a + i))) := by
  refine WP.seq (WP.of_funs (WP.of_syms (WP.mono (ldFn_ok L R (j := j + 1) (by omega) hjn)
    fun t₁ ⟨h11, hm, hk1⟩ hsy hfu => ?_)))
  obtain ⟨rd', wr', g'⟩ := keep_r11 hk1
  refine WP.mono (upd_ok hT (t := t₁) (by rw [h11, hsk]; exact hF.upd) (hh.keep hm hk1 hfu hsy)
    (L.congr (g' _ (by decide)) wr' (by rw [hm])) (hm ▸ R) ha hda hwa
    (by rw [g' _ (by decide), hdi]) (by rw [g' _ (by decide), hdx]) (by rw [g' _ (by decide), hcx])
    (by rw [g' _ (by decide), h8]))
    fun t' ⟨a, b, c, d, e, f, g⟩ => ⟨a, b.trans rd', c.trans wr', fun r hr => (d r hr).trans
      (g' r (calleeSaved_ne_r11 r hr)), e, f, fun m hm' hsi => g m (hm ▸ hm') (by rw [g' _ (by decide), hsi])⟩

include hT in
/-- `finalize` through the address in the slot `sl + 16`, to `scratch + o`. -/
theorem finF_ok {stack : Nat} {e : State} {fi fu ff : Addr} (hF : Fns stack e T fi fu ff) {t : State}
    {F S : Addr} (hh : Here stack e t F S) (L : Lay t F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep t.mem F S V W) (hj : sl = 8 * j) (hjn : j + 2 < nW) (hsk : W (j + 2) = ff) {o : Nat}
    (ho : o + 64 ≤ oSt ∨ (oSt + 256 ≤ o ∧ o + 64 ≤ oW))
    (hdi : t.gpr .rdi = off S oSt) (hdx : t.gpr .rdx = off S o) (hcx : t.gpr .rcx = off S oW) :
    WP isa (finF sl) t fun t' => Lay t' F S ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧
      (∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) ∧
      Rep t'.mem F S (fun x => if inR [(oSt, T.S.stateBytes), (o, T.outBytes), (oW, 8 * T.scratch)] x then
        t'.mem (off S x) else V x) W ∧ Here stack e t' F S ∧
      (∀ m, T.S.Repr t.mem (off S oSt) m → m.length < 2 ^ 64 → t.gpr .rsi = BitVec.ofNat 64 m.length →
        ∀ i < T.S.digestBytes, t'.mem (off S (o + i)) = (T.S.H.hash m).getD i 0) := by
  refine WP.seq (WP.of_funs (WP.of_syms (WP.mono (ldFn_ok L R (j := j + 2) (by omega) hjn)
    fun t₁ ⟨h11, hm, hk1⟩ hsy hfu => ?_)))
  obtain ⟨rd', wr', g'⟩ := keep_r11 hk1
  refine WP.mono (fin_ok hT (t := t₁) (by rw [h11, hsk]; exact hF.fin) (hh.keep hm hk1 hfu hsy)
    (L.congr (g' _ (by decide)) wr' (by rw [hm])) (hm ▸ R) ho
    (by rw [g' _ (by decide), hdi]) (by rw [g' _ (by decide), hdx]) (by rw [g' _ (by decide), hcx]))
    fun t' ⟨a, b, c, d, e, f, g⟩ => ⟨a, b.trans rd', c.trans wr', fun r hr => (d r hr).trans
      (g' r (calleeSaved_ne_r11 r hr)), e, f, fun m hm' hl hsi => g m (hm ▸ hm') hl
        (by rw [g' _ (by decide), hsi])⟩

include hT in
/-- `update` through the address in the slot `sl + 8`, with the `len` bytes
at `d`, outside our working space. -/
theorem updExtF_ok {stack : Nat} {e : State} {fi fu ff : Addr} (hF : Fns stack e T fi fu ff) {t : State}
    {F S : Addr} (hh : Here stack e t F S) (L : Lay t F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep t.mem F S V W) (hj : sl = 8 * j) (hjn : j + 1 < nW) (hsk : W (j + 1) = fu) {d : Addr}
    {len : Nat} (hlen : len < 2 ^ 64) (hbd : d.toNat + len ≤ 2 ^ 64)
    (hcd : ∀ x, (⟨d, len⟩ : Region).Contains x 1 → InRegions (e.rd ++ e.wr ++ abi.reserved stack e) x 1)
    (hds : Region.Disjoint ⟨d, len⟩ ⟨S, oRsa⟩) (hdk : (below F 16).Disjoint ⟨d, len⟩)
    (hdi : t.gpr .rdi = off S oSt) (hdx : t.gpr .rdx = d) (hcx : t.gpr .rcx = BitVec.ofNat 64 len)
    (h8 : t.gpr .r8 = off S oW) :
    WP isa (updF sl) t fun t' => Lay t' F S ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧
      (∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) ∧
      Rep t'.mem F S (fun o => if inR [(oSt, T.S.stateBytes), (oW, 8 * T.scratch)] o then t'.mem (off S o)
        else V o) W ∧
      Frame (regs S [(oSt, T.S.stateBytes), (oW, 8 * T.scratch)] ++ [retR F]) t.mem t'.mem ∧
      Here stack e t' F S ∧
      (∀ m, T.S.Repr t.mem (off S oSt) m → t.gpr .rsi = BitVec.ofNat 64 m.length →
        T.S.Repr t'.mem (off S oSt) (m ++ Spec.Rsa.bytesAt t.mem d len)) := by
  refine WP.seq (WP.of_funs (WP.of_syms (WP.mono (ldFn_ok L R (j := j + 1) (by omega) hjn)
    fun t₁ ⟨h11, hm, hk1⟩ hsy hfu => ?_)))
  obtain ⟨rd', wr', g'⟩ := keep_r11 hk1
  refine WP.mono (updExt_ok hT (t := t₁) (by rw [h11, hsk]; exact hF.upd) (hh.keep hm hk1 hfu hsy)
    (L.congr (g' _ (by decide)) wr' (by rw [hm])) (hm ▸ R) hlen hbd hcd hds hdk
    (by rw [g' _ (by decide), hdi]) (by rw [g' _ (by decide), hdx]) (by rw [g' _ (by decide), hcx])
    (by rw [g' _ (by decide), h8]))
    fun t' ⟨a, b, c, d', e, f, g, h⟩ => ⟨a, b.trans rd', c.trans wr', fun r hr => (d' r hr).trans
      (g' r (calleeSaved_ne_r11 r hr)), e, hm ▸ f, g,
      fun m hm' hsi => by rw [← hm]; exact h m (hm ▸ hm') (by rw [g' _ (by decide), hsi])⟩

end VG.Proof.RsaOaep.X86_64
