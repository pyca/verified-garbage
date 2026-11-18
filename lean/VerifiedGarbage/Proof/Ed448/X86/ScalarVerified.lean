module

public import VerifiedGarbage.Proof.Ed448.X86.ScalarMain
meta import VerifiedGarbage.Proof.Ed448.X86.ScalarMain
public import VerifiedGarbage.Proof.Ed448.X86.ScalarLit
meta import VerifiedGarbage.Proof.Ed448.X86.ScalarLit
public import VerifiedGarbage.Proof.Framework.X86.Inline
meta import VerifiedGarbage.Proof.Framework.X86.Inline
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Ed448.ScalarWords
import VerifiedGarbage.Proof.Ed448.X86.ScalarMulAdd
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.Mmx
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.X25519.X86.Basic
import VerifiedGarbage.Proof.X448.Bytes
import VerifiedGarbage.Proof.X448.X86.Carry
import VerifiedGarbage.Proof.X448.X86.Columns
import VerifiedGarbage.Proof.X448.X86.Copy
import VerifiedGarbage.Proof.X448.X86.FnVerified
import VerifiedGarbage.Proof.X448.X86.Frame
import VerifiedGarbage.Proof.X448.X86.Freeze
import VerifiedGarbage.Proof.X448.X86.Ops
import VerifiedGarbage.Proof.X448.X86.Restore
import VerifiedGarbage.Proof.X448.X86.Select
import VerifiedGarbage.Proof.X448.X86.Small
import VerifiedGarbage.Proof.X448.X86.Step
meta import VerifiedGarbage.Proof.Ed448.ScalarWords
meta import VerifiedGarbage.Proof.Ed448.X86.ScalarMulAdd
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86.CallWith
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Mmx
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.X25519.X86.Basic
meta import VerifiedGarbage.Proof.X448.Bytes
meta import VerifiedGarbage.Proof.X448.X86.Carry
meta import VerifiedGarbage.Proof.X448.X86.Columns
meta import VerifiedGarbage.Proof.X448.X86.Copy
meta import VerifiedGarbage.Proof.X448.X86.FnVerified
meta import VerifiedGarbage.Proof.X448.X86.Frame
meta import VerifiedGarbage.Proof.X448.X86.Freeze
meta import VerifiedGarbage.Proof.X448.X86.Ops
meta import VerifiedGarbage.Proof.X448.X86.Restore
meta import VerifiedGarbage.Proof.X448.X86.Select
meta import VerifiedGarbage.Proof.X448.X86.Small
meta import VerifiedGarbage.Proof.X448.X86.Step
public import VerifiedGarbage.Spec.Ed448.Contract
public import VerifiedGarbage.Proof.Ed448.X86.ScalarIO
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Ed448.X86.ScalarIO
meta import VerifiedGarbage.Proof.Framework.Lit

/-! ### `Ed448.X86.ScalarMulAddMain`, which this module and modules that import it used -/

section

/-!
# Ed448 scalar multiply-add on x86 (32-bit): the whole function

`vg_ed448_scalar_mul_add(out = [esp + 4], r = [esp + 8], k = [esp + 12],
s = [esp + 16], scratch = [esp + 20])` against a local contract
(`scalarMulAddLocal`: the arguments only read), the ABI included.
-/

@[expose] public section

namespace VG.Proof.Ed448.X86

open VG VG.X86 VG.Proof.X448.Radix16 VG.Proof.X448.X86 VG.Proof.Ed448.Limbs16
open VG.Impl.Ed448.X86 (W TF RA SK SS SR scalarMulAdd inputs reduceT finish)
open VG.Spec.Ed448 (L bytesAt decodeLE encodeLE)

/-- `vg_ed448_scalar_mul_add(out, r, k, s, scratch)`, whose arguments are on
the stack (cdecl). -/
def scalarMulAddLocal : Contract isa where
  pre s :=
    let out : Region := ⟨(arg s 0).setWidth 64, 57⟩
    let r : Region := ⟨(arg s 1).setWidth 64, 57⟩
    let k : Region := ⟨(arg s 2).setWidth 64, 57⟩
    let a : Region := ⟨(arg s 3).setWidth 64, 57⟩
    let scratch : Region := ⟨(arg s 4).setWidth 64, 8192⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [r, k, a, args] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧
      r.Disjoint scratch ∧ k.Disjoint scratch ∧ a.Disjoint scratch ∧ args.Disjoint out ∧
      args.Disjoint scratch ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧
      (arg s 0).toNat + 57 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 57 ≤ 2 ^ 32 ∧
      (arg s 2).toNat + 57 ≤ 2 ^ 32 ∧ (arg s 3).toNat + 57 ≤ 2 ^ 32 ∧
      (arg s 4).toNat + 8192 ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 24 ≤ 2 ^ 32
  post s t := bytesAt t.mem ((arg s 0).setWidth 64) 57 =
    Spec.Ed448.scalarMulAdd (bytesAt s.mem ((arg s 1).setWidth 64) 57)
      (bytesAt s.mem ((arg s 2).setWidth 64) 57) (bytesAt s.mem ((arg s 3).setWidth 64) 57)
  pub s t := s.gpr .esp = t.gpr .esp ∧ arg s 0 = arg t 0 ∧ arg s 1 = arg t 1 ∧ arg s 2 = arg t 2 ∧
    arg s 3 = arg t 3 ∧ arg s 4 = arg t 4

/-- The precondition, by name. -/
structure MulAddPre (s : State) : Prop where
  rd : s.rd = [⟨(arg s 1).setWidth 64, 57⟩, ⟨(arg s 2).setWidth 64, 57⟩,
    ⟨(arg s 3).setWidth 64, 57⟩, ⟨argAddr s 0, 20⟩]
  wr : s.wr = [⟨(arg s 0).setWidth 64, 57⟩, scR (arg s 4)]
  out_sc : (⟨(arg s 0).setWidth 64, 57⟩ : Region).Disjoint (scR (arg s 4))
  r_sc : (⟨(arg s 1).setWidth 64, 57⟩ : Region).Disjoint (scR (arg s 4))
  k_sc : (⟨(arg s 2).setWidth 64, 57⟩ : Region).Disjoint (scR (arg s 4))
  a_sc : (⟨(arg s 3).setWidth 64, 57⟩ : Region).Disjoint (scR (arg s 4))
  args_out : (⟨argAddr s 0, 20⟩ : Region).Disjoint ⟨(arg s 0).setWidth 64, 57⟩
  args_sc : (⟨argAddr s 0, 20⟩ : Region).Disjoint (scR (arg s 4))
  ret_out : (retR s).Disjoint ⟨(arg s 0).setWidth 64, 57⟩
  ret_sc : (retR s).Disjoint (scR (arg s 4))
  out_fit : (arg s 0).toNat + 57 ≤ 2 ^ 32
  r_fit : (arg s 1).toNat + 57 ≤ 2 ^ 32
  k_fit : (arg s 2).toNat + 57 ≤ 2 ^ 32
  a_fit : (arg s 3).toNat + 57 ≤ 2 ^ 32
  sc_fit : (arg s 4).toNat + 8192 ≤ 2 ^ 32
  sp_fit : (s.gpr .esp).toNat + 24 ≤ 2 ^ 32

theorem MulAddPre.of {s : State} (h : scalarMulAddLocal.pre s) : MulAddPre s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩

theorem MulAddPre.args {s : State} (h : MulAddPre s) : Args s 5 4 :=
  ⟨by rw [h.rd]; simp, by have := h.sp_fit; omega_using [this], by decide, by rw [h.wr]; simp, h.sc_fit,
    h.args_sc, h.ret_sc⟩

theorem MulAddPre.input {s : State} (h : MulAddPre s) {base : Addr} (hbase : (arg s 4).setWidth 64 = base)
    {i : Nat} (h1 : 1 ≤ i) (h4 : i < 4) : Input s base (arg s i) 57 := by
  subst hbase
  rcases (by omega_using [h1, h4] : i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl
  · exact Input.of_region h.r_fit (by rw [h.rd]; simp) h.r_sc
  · exact Input.of_region h.k_fit (by rw [h.rd]; simp) h.k_sc
  · exact Input.of_region h.a_fit (by rw [h.rd]; simp) h.a_sc

theorem mulAdd_mod (r k s : Nat) : ((k % L * (s % L)) % L + r % L) % L = (r + k * s) % L := by
  rw [← Nat.mul_mod, ← Nat.add_mod, Nat.add_comm]

/-- What a step of multiply-add changes: the registers but `esp`, and the
working space above the saved registers. -/
structure MKeep (base : Addr) (s t : State) : Prop where
  regs : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t
  mem : Outside base 16 8176 s.mem t.mem

theorem MKeep.trans {base : Addr} {s t u : State} (h : MKeep base s t) (h' : MKeep base t u) :
    MKeep base s u := ⟨h.regs.trans h'.regs, h.mem.trans h'.mem⟩

theorem MKeep.whole {base : Addr} {s t : State} (h : MKeep base s t) : Outside base 0 8192 s.mem t.mem :=
  h.mem.mono (by omega_using []) (by omega_using [])

theorem MKeep.of2 {base : Addr} {s t : State} {rs : List Reg} (hr : Keeps rs s t)
    (hrs : ∀ r ∈ rs, r ∈ [Reg.eax, .ebx, .ecx, .edx, .ebp, .esi])
    {x nx y ny : Nat} (hm : Outside2 base x nx y ny s.mem t.mem) (hx : 16 ≤ x) (hy : 16 ≤ y)
    (hx' : x + nx ≤ 8192) (hy' : y + ny ≤ 8192) : MKeep base s t :=
  ⟨hr.mono hrs, fun p hp => hm p (by omega_using [hx, hx', hp]) (by omega_using [hy, hy', hp])⟩

theorem MKeep.of1 {base : Addr} {s t : State} {rs : List Reg} (hr : Keeps rs s t)
    (hrs : ∀ r ∈ rs, r ∈ [Reg.eax, .ebx, .ecx, .edx, .ebp, .esi])
    {x nx : Nat} (hm : Outside base x nx s.mem t.mem) (hx : 16 ≤ x) (hx' : x + nx ≤ 8192) :
    MKeep base s t :=
  ⟨hr.mono hrs, fun p hp => hm p (by omega_using [hx, hx', hp])⟩

theorem inputs_ok {s₀ s : State} (h : MulAddPre s₀) {base : Addr} (hbase : (arg s₀ 4).setWidth 64 = base)
    (hsp : s.gpr .esp = s₀.gpr .esp) (hr : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hm : Outside base 0 8192 s₀.mem s.mem) (hs : Scr s base) :
    WP isa inputs s fun t => MKeep base s t ∧
      Bounded t.mem base SK ∧ Bounded t.mem base SS ∧ Bounded t.mem base SR ∧
      fe t.mem base SK = decodeLE (bytesAt s₀.mem ((arg s₀ 2).setWidth 64) 57) % L ∧
      fe t.mem base SS = decodeLE (bytesAt s₀.mem ((arg s₀ 3).setWidth 64) 57) % L ∧
      fe t.mem base SR = decodeLE (bytesAt s₀.mem ((arg s₀ 1).setWidth 64) 57) % L := by
  have hA := h.args
  have hK := SK_eq
  have hS := SS_eq
  have hR := SR_eq
  unfold inputs
  refine WP.seq (WP.mono (reduceArg_ok (i := 2) hA hbase hsp hr hwr hm hs (by decide)
    (o := SK) ⟨by decide, by decide⟩ (h.input hbase (by decide) (by decide)))
    fun u ⟨ku, mu, lu, vu⟩ => ?_)
  obtain mu' : MKeep base s u := MKeep.of2 ku (by decide) mu (by decide) (by decide) (by decide) (by decide)
  refine WP.seq (WP.mono (reduceArg_ok (i := 3) hA hbase ((ku.1 _ (by decide)).trans hsp)
    (ku.2.1.trans hr) (ku.2.2.trans hwr) (hm.trans mu'.whole) (hs.of_keeps ku (by decide)) (by decide)
    (o := SS) ⟨by decide, by decide⟩ (h.input hbase (by decide) (by decide)))
    fun v ⟨kv, mv, lv, vv⟩ => ?_)
  obtain mv' : MKeep base u v := MKeep.of2 kv (by decide) mv (by decide) (by decide) (by decide) (by decide)
  refine WP.mono (reduceArg_ok (i := 1) hA hbase ((kv.1 _ (by decide)).trans ((ku.1 _ (by decide)).trans hsp))
    (kv.2.1.trans (ku.2.1.trans hr)) (kv.2.2.trans (ku.2.2.trans hwr))
    ((hm.trans mu'.whole).trans mv'.whole) ((hs.of_keeps ku (by decide)).of_keeps kv (by decide))
    (by decide) (o := SR) ⟨by decide, by decide⟩ (h.input hbase (by decide) (by decide)))
    fun t ⟨kt, mt, lt, vt⟩ => ?_
  obtain mt' : MKeep base v t := MKeep.of2 kt (by decide) mt (by decide) (by decide) (by decide) (by decide)
  obtain eK : ∀ j < 28, limbs t.mem base SK j = limbs u.mem base SK j := fun j hj => by
    show (word t.mem base (SK + 4 * j)).toNat = (word u.mem base (SK + 4 * j)).toNat
    rw [congrArg BitVec.toNat (mt.word (d := SK + 4 * j) (Or.inr (by simp only [W]; omega_using [hK]))
      (Or.inl (by omega_using [hK, hR, hj])) (by omega_using [hK, hj])),
      congrArg BitVec.toNat (mv.word (d := SK + 4 * j) (Or.inr (by simp only [W]; omega_using [hK]))
      (Or.inl (by omega_using [hK, hS, hj])) (by omega_using [hK, hj]))]
  obtain eS : ∀ j < 28, limbs t.mem base SS j = limbs v.mem base SS j := fun j hj =>
    congrArg BitVec.toNat (mt.word (d := SS + 4 * j) (Or.inr (by simp only [W]; omega_using [hS]))
      (Or.inl (by omega_using [hS, hR, hj])) (by omega_using [hS, hj]))
  exact ⟨mu'.trans (mv'.trans mt'), fun j hj => by rw [eK j hj]; exact lu j hj,
    fun j hj => by rw [eS j hj]; exact lv j hj, lt, by rw [← vu]; exact valN_congr eK,
    by rw [← vv]; exact valN_congr eS, vt⟩

theorem scalarMulAdd_correct {s₀ : State} (h : MulAddPre s₀) :
    WP isa scalarMulAdd s₀ fun t => abiPreserved s₀ t ∧ scalarMulAddLocal.post s₀ t := by
  have hA := h.args
  obtain ⟨base, hbase⟩ : ∃ b, (arg s₀ 4).setWidth 64 = b := ⟨_, rfl⟩
  have hT := TF_eq
  have hK := SK_eq
  have hS := SS_eq
  have hR := SR_eq
  have hRA := RA_eq
  have hC := ACC_eq
  unfold scalarMulAdd
  refine WP.seq (WP.mono (save_ok hA) fun s1 ⟨hs1, sv1, o1, k1⟩ => ?_)
  rw [hbase] at hs1 sv1 o1
  obtain o1' : Outside base 0 8192 s₀.mem s1.mem := o1.mono (by omega_using []) (by omega_using [])
  -- the inputs
  refine WP.seq (WP.mono (inputs_ok h hbase (k1.1 _ (by decide)) k1.2.1 k1.2.2 o1' hs1)
    fun s2 ⟨k2, lK, lS, lR, vK, vS, vR⟩ => ?_)
  obtain hs2 := hs1.of_keeps k2.regs (by decide)
  -- the product
  refine WP.seq (WP.mono (product_ok hs2 lK lS) fun s3 ⟨hs3, k3, m3, a3, v3⟩ => ?_)
  obtain k3' : MKeep base s2 s3 := MKeep.of1 k3 (by decide) m3 (by decide) (by decide)
  -- its reduction
  refine WP.seq (WP.mono (reduceProduct_ok hs3 a3) fun s4 ⟨k4, l4, v4⟩ => ?_)
  obtain hs4 := hs3.of_keeps k4.regs (by decide)
  obtain k4' : MKeep base s3 s4 := MKeep.of2 k4.regs (by decide) k4.mem (by decide) (by decide)
    (by decide) (by decide)
  -- the reduced `r` survives the product and its reduction
  obtain eR : ∀ j < 28, limbs s4.mem base SR j = limbs s2.mem base SR j := fun j hj => by
    show (word s4.mem base (SR + 4 * j)).toNat = (word s2.mem base (SR + 4 * j)).toNat
    rw [congrArg BitVec.toNat (k4.mem.word (d := SR + 4 * j) (Or.inr (by simp only [W]; omega_using [hR]))
      (Or.inr (by omega_using [hR, hRA])) (by omega_using [hR, hj])),
      congrArg BitVec.toNat (m3.word (d := SR + 4 * j) (Or.inl (by omega_using [hR, hC, hj])) (by omega_using [hR, hj]))]
  obtain lR4 : Bounded s4.mem base SR := fun j hj => by rw [eR j hj]; exact lR j hj
  obtain vR4 : fe s4.mem base SR = fe s2.mem base SR := valN_congr eR
  obtain hvR : fe s4.mem base SR < L := by rw [vR4, vR]; exact Nat.mod_lt _ Proof.Ed448.L_pos
  obtain hvA : fe s4.mem base RA < L := by rw [v4]; exact Nat.mod_lt _ Proof.Ed448.L_pos
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (addPass_ok hs4 l4 lR4 hvA hvR) fun s5 ⟨k5, m5, l5, v5⟩ => ?_
  obtain hs5 := hs4.of_keeps k5 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (reduceT_ok RA_buf hs5 l5 (by rw [v5]; omega_using [hvR, hvA])) fun s6 ⟨k6, m6, l6, v6⟩ => ?_
  obtain hs6 := hs5.of_keeps k6 (by decide)
  obtain k5' : MKeep base s4 s5 := MKeep.of1 k5 (by decide) m5 (by decide) (by decide)
  obtain k6' : MKeep base s5 s6 := MKeep.of1 k6 (by decide) m6 (by decide) (by decide)
  obtain kall : MKeep base s1 s6 := k2.trans (k3'.trans (k4'.trans (k5'.trans k6')))
  obtain m06 : Outside base 0 8192 s₀.mem s6.mem := o1'.trans kall.whole
  obtain sv6 : Saved base s₀.gpr s6.mem := sv1.outside kall.mem (by decide)
  obtain k06 : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi, .edi] s₀ s6 :=
    (k1.mono (by decide)).trans (kall.regs.mono (by decide))
  refine WP.mono (finish_ok hA (by decide) (k06.1 _ (by decide)) k06.2.1 k06.2.2 hbase m06 hs6
    (by decide) l6 (by rw [h.wr]; simp) h.out_fit (fun j hj => far_out (hbase ▸ h.out_sc) hj)
    sv6) fun t ⟨tr, kt, ot, bt⟩ => ⟨⟨?_, ?_⟩, ?_⟩
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact tr (.ebx, 0) (by decide)
    · exact tr (.esi, 4) (by decide)
    · exact tr (.edi, 8) (by decide)
    · exact tr (.ebp, 12) (by decide)
    · rw [kt.1 _ (by decide), k06.1 _ (by decide)]
  · exact abi_of hbase h.ret_sc h.ret_out m06 ot
  · change bytesAt t.mem _ 57 = encodeLE 57 _
    rw [bt, v6, v5, v4, v3, vR4, vK, vS, vR, mulAdd_mod]

end VG.Proof.Ed448.X86

end

end

/-!
# Ed448 scalar arithmetic on x86 (32-bit): `Verified`

Correctness includes the ABI. Taint analysis checks that secret input bytes
never determine branches or memory addresses: the only branches are on the
loop counters, and every address is a pointer plus a constant or a counter.
The local contracts only read the arguments; the shared contract of `Spec/`
lets the code write them too (`writeArgs`), which it does not
(`Verified.narrowTo`). A concrete witness proves it satisfiable.
-/

@[expose] public section

namespace VG.Proof.Ed448.X86

open VG VG.X86 VG.Proof.X448.X86
open VG.Impl.Ed448.X86 (scalarReduce scalarMulAdd)

/-- The taint analysis starts with the stack arguments public, and the words
holding `out` and `scratch` (argument `scidx` of `argc`) known to be the base
addresses of the writable regions. -/
def scalarTaint (scidx argc : Nat) : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [57, 8192], argLen := 4 + 4 * argc,
    argBases := [(4, 0), (4 + 4 * scidx, 1)] }

theorem scalarTaint_wf {s : State} {argc scidx : Nat} (hp : Args s argc scidx)
    (hw : s.wr = [⟨(arg s 0).setWidth 64, 57⟩, scR (arg s scidx)])
    (hos : (⟨(arg s 0).setWidth 64, 57⟩ : Region).Disjoint (scR (arg s scidx)))
    (hofit : (arg s 0).toNat + 57 ≤ 2 ^ 32)
    (hret : (retR s).Disjoint ⟨(arg s 0).setWidth 64, 57⟩)
    (hao : (⟨argAddr s 0, 4 * argc⟩ : Region).Disjoint ⟨(arg s 0).setWidth 64, 57⟩) :
    VG.X86.Taint.Wf (scalarTaint scidx argc) s := by
  have hf := hp.sc_fit; have spfit := hp.sp_fit
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun _ => ⟨by simp [hw, scalarTaint], by simpa [hw] using hos, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨by change (s.gpr .esp).toNat + (4 + 4 * argc) ≤ 2 ^ 32; omega_using [spfit], ?_⟩, ?_⟩
  · simp only [hw, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [BitVec.toNat_setWidth] <;> omega_using [hf, hofit]
  · simp only [hw, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 4 * argc) (by omega_using [spfit]) hret hao
    · exact VG.X86.Taint.frame_disjoint (n := 4 * argc) (by omega_using [spfit]) hp.ret_sc hp.args_sc
  · intro p hp'
    simp only [scalarTaint, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl
    · refine ⟨by dsimp only [scalarTaint]; have := hp.sc_lt; omega_using [this], ?_⟩
      simp [VG.X86.Taint.region, hw, VG.X86.addr, arg, argAddr]
    · refine ⟨by dsimp only [scalarTaint]; have := hp.sc_lt; omega_using [this], ?_⟩
      simp [VG.X86.Taint.region, hw, VG.X86.addr, arg, argAddr]

theorem scalarTaint_agree {s t : State} {scidx argc : Nat}
    (hs : VG.X86.Taint.Wf (scalarTaint scidx argc) s) (ht : VG.X86.Taint.Wf (scalarTaint scidx argc) t)
    (hsp : s.gpr .esp = t.gpr .esp) (ha : ∀ i < argc, arg s i = arg t i)
    (hi : scidx < argc)
    (hws : s.wr = [⟨(arg s 0).setWidth 64, 57⟩, scR (arg s scidx)])
    (hwt : t.wr = [⟨(arg t 0).setWidth 64, 57⟩, scR (arg t scidx)])
    (hss : (s.gpr .esp).toNat + 4 + 4 * argc ≤ 2 ^ 32)
    (hst : (t.gpr .esp).toNat + 4 + 4 * argc ≤ 2 ^ 32) :
    VG.X86.Taint.Agree (scalarTaint scidx argc) s t := by
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, hs, ht,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => hsp,
    fun k h4 hk => ?_⟩
  · simp only [scalarTaint, RegSet.mem_ofList, List.mem_singleton] at hr
    subst hr; exact hsp
  · rw [hws, hwt, ha 0 (by omega_using [hi]), ha scidx hi]
  · simp only [scalarTaint] at hk
    rw [show VG.X86.Taint.depth (scalarTaint scidx argc).stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (by omega_using [hss]) h4 hk,
      VG.X86.Taint.argByte_eq (by omega_using [hst]) h4 hk,
      Mem.readW_byte s.mem _ (Nat.mod_lt _ (by decide)),
      Mem.readW_byte t.mem _ (Nat.mod_lt _ (by decide))]
    exact congrArg _ (ha ((k - 4) / 4) (by omega_using [hk, h4]))

/-! ## Reduction -/

theorem scalarReduce_wf {s : State} (h : scalarReduceLocal.pre s) :
    VG.X86.Taint.Wf (scalarTaint 2 3) s := by
  have hp := ReducePre.of h
  exact scalarTaint_wf hp.args hp.wr hp.out_sc hp.out_fit hp.ret_out hp.args_out

theorem scalarReduce_ct :
    ConstantTime isa scalarReduceLocal.pre scalarReduceLocal.pub scalarReduce := by
  refine VG.Taint.constantTime (A := taint) (scalarTaint 2 3) ?_ (by taint_decide)
  intro s t hs ht hp
  obtain ⟨sp, a0, a1, a2⟩ := hp
  have ps := ReducePre.of hs
  have pt := ReducePre.of ht
  refine scalarTaint_agree (scalarReduce_wf hs) (scalarReduce_wf ht) sp ?_ (by decide)
    ps.wr pt.wr ps.args.sp_fit pt.args.sp_fit
  intro i hi
  rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
  exacts [a0, a1, a2]

theorem scalarReduce_ok (s : State) (h : scalarReduceLocal.pre s) :
    ∃ tr t, Exec isa scalarReduce s tr t ∧ abiPreserved s t ∧ scalarReduceLocal.post s t :=
  scalarReduce_correct (ReducePre.of h)

/-! ## Multiply-add -/

theorem scalarMulAdd_wf {s : State} (h : scalarMulAddLocal.pre s) :
    VG.X86.Taint.Wf (scalarTaint 4 5) s := by
  have hp := MulAddPre.of h
  exact scalarTaint_wf hp.args hp.wr hp.out_sc hp.out_fit hp.ret_out hp.args_out

theorem scalarMulAdd_ct :
    ConstantTime isa scalarMulAddLocal.pre scalarMulAddLocal.pub scalarMulAdd := by
  refine VG.Taint.constantTime (A := taint) (scalarTaint 4 5) ?_ (by taint_decide)
  intro s t hs ht hp
  obtain ⟨sp, a0, a1, a2, a3, a4⟩ := hp
  have ps := MulAddPre.of hs
  have pt := MulAddPre.of ht
  refine scalarTaint_agree (scalarMulAdd_wf hs) (scalarMulAdd_wf ht) sp ?_ (by decide)
    ps.wr pt.wr ps.args.sp_fit pt.args.sp_fit
  intro i hi
  rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl
  exacts [a0, a1, a2, a3, a4]

theorem scalarMulAdd_ok (s : State) (h : scalarMulAddLocal.pre s) :
    ∃ tr t, Exec isa scalarMulAdd s tr t ∧ abiPreserved s t ∧ scalarMulAddLocal.post s t :=
  scalarMulAdd_correct (MulAddPre.of h)

end VG.Proof.Ed448.X86
