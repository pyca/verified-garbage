import VerifiedGarbage.Proof.Ed448.X86.ScalarMulAdd

/-!
# Ed448 scalar multiply-add on x86 (32-bit): the whole function

`vg_ed448_scalar_mul_add(out = [esp + 4], r = [esp + 8], k = [esp + 12],
s = [esp + 16], scratch = [esp + 20])` against a local contract
(`scalarMulAddLocal`: the arguments only read), the ABI included.
-/

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
  ⟨by rw [h.rd]; simp, by have := h.sp_fit; omega, by decide, by rw [h.wr]; simp, h.sc_fit,
    h.args_sc, h.ret_sc⟩

theorem MulAddPre.input {s : State} (h : MulAddPre s) {base : Addr} (hbase : (arg s 4).setWidth 64 = base)
    {i : Nat} (h1 : 1 ≤ i) (h4 : i < 4) : Input s base (arg s i) 57 := by
  subst hbase
  rcases (by omega : i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl
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
  h.mem.mono (by omega) (by omega)

theorem MKeep.of2 {base : Addr} {s t : State} {rs : List Reg} (hr : Keeps rs s t)
    (hrs : ∀ r ∈ rs, r ∈ [Reg.eax, .ebx, .ecx, .edx, .ebp, .esi])
    {x nx y ny : Nat} (hm : Outside2 base x nx y ny s.mem t.mem) (hx : 16 ≤ x) (hy : 16 ≤ y)
    (hx' : x + nx ≤ 8192) (hy' : y + ny ≤ 8192) : MKeep base s t :=
  ⟨hr.mono hrs, fun p hp => hm p (by omega) (by omega)⟩

theorem MKeep.of1 {base : Addr} {s t : State} {rs : List Reg} (hr : Keeps rs s t)
    (hrs : ∀ r ∈ rs, r ∈ [Reg.eax, .ebx, .ecx, .edx, .ebp, .esi])
    {x nx : Nat} (hm : Outside base x nx s.mem t.mem) (hx : 16 ≤ x) (hx' : x + nx ≤ 8192) :
    MKeep base s t :=
  ⟨hr.mono hrs, fun p hp => hm p (by omega)⟩

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
  have mu' : MKeep base s u := MKeep.of2 ku (by decide) mu (by decide) (by decide) (by decide) (by decide)
  refine WP.seq (WP.mono (reduceArg_ok (i := 3) hA hbase ((ku.1 _ (by decide)).trans hsp)
    (ku.2.1.trans hr) (ku.2.2.trans hwr) (hm.trans mu'.whole) (hs.of_keeps ku (by decide)) (by decide)
    (o := SS) ⟨by decide, by decide⟩ (h.input hbase (by decide) (by decide)))
    fun v ⟨kv, mv, lv, vv⟩ => ?_)
  have mv' : MKeep base u v := MKeep.of2 kv (by decide) mv (by decide) (by decide) (by decide) (by decide)
  refine WP.mono (reduceArg_ok (i := 1) hA hbase ((kv.1 _ (by decide)).trans ((ku.1 _ (by decide)).trans hsp))
    (kv.2.1.trans (ku.2.1.trans hr)) (kv.2.2.trans (ku.2.2.trans hwr))
    ((hm.trans mu'.whole).trans mv'.whole) ((hs.of_keeps ku (by decide)).of_keeps kv (by decide))
    (by decide) (o := SR) ⟨by decide, by decide⟩ (h.input hbase (by decide) (by decide)))
    fun t ⟨kt, mt, lt, vt⟩ => ?_
  have mt' : MKeep base v t := MKeep.of2 kt (by decide) mt (by decide) (by decide) (by decide) (by decide)
  have eK : ∀ j < 28, limbs t.mem base SK j = limbs u.mem base SK j := fun j hj => by
    show (word t.mem base (SK + 4 * j)).toNat = (word u.mem base (SK + 4 * j)).toNat
    rw [congrArg BitVec.toNat (mt.word (d := SK + 4 * j) (Or.inr (by simp only [W]; omega))
      (Or.inl (by omega)) (by omega)),
      congrArg BitVec.toNat (mv.word (d := SK + 4 * j) (Or.inr (by simp only [W]; omega))
      (Or.inl (by omega)) (by omega))]
  have eS : ∀ j < 28, limbs t.mem base SS j = limbs v.mem base SS j := fun j hj =>
    congrArg BitVec.toNat (mt.word (d := SS + 4 * j) (Or.inr (by simp only [W]; omega))
      (Or.inl (by omega)) (by omega))
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
  have o1' : Outside base 0 8192 s₀.mem s1.mem := o1.mono (by omega) (by omega)
  -- the inputs
  refine WP.seq (WP.mono (inputs_ok h hbase (k1.1 _ (by decide)) k1.2.1 k1.2.2 o1' hs1)
    fun s2 ⟨k2, lK, lS, lR, vK, vS, vR⟩ => ?_)
  have hs2 := hs1.of_keeps k2.regs (by decide)
  -- the product
  refine WP.seq (WP.mono (product_ok hs2 lK lS) fun s3 ⟨hs3, k3, m3, a3, v3⟩ => ?_)
  have k3' : MKeep base s2 s3 := MKeep.of1 k3 (by decide) m3 (by decide) (by decide)
  -- its reduction
  refine WP.seq (WP.mono (reduceProduct_ok hs3 a3) fun s4 ⟨k4, l4, v4⟩ => ?_)
  have hs4 := hs3.of_keeps k4.regs (by decide)
  have k4' : MKeep base s3 s4 := MKeep.of2 k4.regs (by decide) k4.mem (by decide) (by decide)
    (by decide) (by decide)
  -- the reduced `r` survives the product and its reduction
  have eR : ∀ j < 28, limbs s4.mem base SR j = limbs s2.mem base SR j := fun j hj => by
    show (word s4.mem base (SR + 4 * j)).toNat = (word s2.mem base (SR + 4 * j)).toNat
    rw [congrArg BitVec.toNat (k4.mem.word (d := SR + 4 * j) (Or.inr (by simp only [W]; omega))
      (Or.inr (by omega)) (by omega)),
      congrArg BitVec.toNat (m3.word (d := SR + 4 * j) (Or.inl (by omega)) (by omega))]
  have lR4 : Bounded s4.mem base SR := fun j hj => by rw [eR j hj]; exact lR j hj
  have vR4 : fe s4.mem base SR = fe s2.mem base SR := valN_congr eR
  have hvR : fe s4.mem base SR < L := by rw [vR4, vR]; exact Nat.mod_lt _ Proof.Ed448.L_pos
  have hvA : fe s4.mem base RA < L := by rw [v4]; exact Nat.mod_lt _ Proof.Ed448.L_pos
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (addPass_ok hs4 l4 lR4 hvA hvR) fun s5 ⟨k5, m5, l5, v5⟩ => ?_
  have hs5 := hs4.of_keeps k5 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (reduceT_ok RA_buf hs5 l5 (by rw [v5]; omega)) fun s6 ⟨k6, m6, l6, v6⟩ => ?_
  have hs6 := hs5.of_keeps k6 (by decide)
  have k5' : MKeep base s4 s5 := MKeep.of1 k5 (by decide) m5 (by decide) (by decide)
  have k6' : MKeep base s5 s6 := MKeep.of1 k6 (by decide) m6 (by decide) (by decide)
  have kall : MKeep base s1 s6 := k2.trans (k3'.trans (k4'.trans (k5'.trans k6')))
  have m06 : Outside base 0 8192 s₀.mem s6.mem := o1'.trans kall.whole
  have sv6 : Saved base s₀.gpr s6.mem := sv1.outside kall.mem (by decide)
  have k06 : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi, .edi] s₀ s6 :=
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
