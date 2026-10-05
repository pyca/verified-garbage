import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.Ed448.X86_64.Scalar
import VerifiedGarbage.Proof.Ed448.X86_64.BaseVerified
import VerifiedGarbage.Proof.X448.X86_64.Verified
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Ed448.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86_64.ScalarLit`. -/
section

/-!
# Ed448 scalar arithmetic on x86-64: the code as literals

The kernel checks each literal once; the taint and instruction checks reuse it.
-/

namespace VG

materialize_code Impl.Ed448.X86_64.scalarReduce
materialize_code Impl.Ed448.X86_64.scalarMulAdd

end VG

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86_64.ScalarMulAdd`. -/
section

/-!
# Ed448 scalar multiply-add on x86-64

`vg_ed448_scalar_mul_add` reduces `k`, `s` and `r` (57 bytes each) modulo
`L` with the loop of `vg_ed448_scalar_reduce`, multiplies the first two
with X448's product scanning (`columns`) into `ACC`, reduces the product's
fourteen words with the same loop, adds the third and reduces once more.
-/

namespace VG.Proof.Ed448.X86_64

open VG VG.X86_64 VG.Impl.Ed448.X86_64
open VG.Proof.X448.X86_64 (Keeps Scr rv mv wv word off Outside ofs Saved saved_lt writeW_outside
  word_writeW_self contains_sc)
open VG.Impl.X448.X86_64 (W w sc at_ saved loads stores chain)
open VG.Spec.Ed448 (L bytesAt decodeLE)

/-- `reduce57`: the remainder of the 57 bytes at `rsi`, a buffer outside the
working space. -/
theorem reduce57_ok {s : State} {base : Addr} (hs : Scr s base)
    (hK : mv s.mem base KC 7 = wv kWords)
    (hR : (⟨s.gpr .rsi, 57⟩ : Region) ∈ s.rd ++ s.wr)
    (hfar : ∀ i < 57, 8192 ≤ ofs base (s.gpr .rsi + BitVec.ofNat 64 i)) :
    WP isa reduce57 s fun t =>
      rem t = decodeLE (bytesAt s.mem (s.gpr .rsi) 57) % L ∧
      (∀ r, r ∉ bodyClob → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Outside base TMP 56 s.mem t.mem := by
  rw [reduce57]
  apply WP.seq
  refine WP.mono (init57_ok s ⟨_, hR, Offset.contains_base _ (by omega) (by omega)⟩)
    fun s₁ ⟨v₁, b₁, k₁⟩ => ?_
  have hs₁ : Scr s₁ base := hs.of_keeps k₁ (by decide)
  have rsi₁ : s₁.gpr .rsi = s.gpr .rsi := k₁.1 _ (by decide)
  have v₁' : rem s₁ = decodeLE (bytesAt s₁.mem (s₁.gpr .rsi + BitVec.ofNat 64 (8 * 7))
      (57 - 8 * 7)) % L := by
    rw [v₁, k₁.2.1, rsi₁]
    refine (Nat.mod_eq_of_lt ?_).symm
    have := decodeLE_lt' (bytesAt s.mem (s.gpr .rsi + BitVec.ofNat 64 56) 1)
    rw [VG.Proof.Ed448.X86_64.bytesAt_length] at this
    have : 256 < L := by decide +kernel
    omega
  refine WP.mono (scalarLoop_ok hs₁ (by rw [k₁.2.1]; exact hK) (len := 57) (n₀ := 7)
    (by decide) (by decide) ⟨by decide, b₁, v₁', fun _ _ => rfl, rfl, rfl, Outside.refl _ _ _ _⟩
    (fun k hk => by
      rw [rsi₁, k₁.2.2.1, k₁.2.2.2]
      exact ⟨_, hR, Offset.contains_base _ (d := 8 * k) (n := 8) (k := 57) (by omega) (by omega)⟩)
    (fun i hi => Or.inr (by rw [rsi₁]; have := hfar i hi; simp only [TMP]; omega)))
    fun t ⟨vt, gt, rdt, wrt, ot⟩ => ?_
  refine ⟨by rw [vt, rsi₁, k₁.2.1], fun r hr => ?_, by rw [rdt, k₁.2.2.1], by rw [wrt, k₁.2.2.2],
    by rw [← k₁.2.1]; exact ot⟩
  have sub : ∀ x ∈ Reg.rbx :: W, x ∈ bodyClob := by decide
  rw [gt r hr, k₁.1 r (fun h => hr (sub r h))]

open VG.Proof.X448.X86_64 (colX acc columns_ok mulCol_hc mulCol_hw mulCols_sum mv7 rvW val7
  zeroAcc_ok w_colX rdi_colX stable_sc loads_ok W_nodup W_len prod_lt)
/-- The product of `[SK]` and `[SS]` (each below `L`) into the fourteen words
at `ACC`. -/
theorem product_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block product) s fun t => mv t.mem base Impl.X448.X86_64.ACC 14 = mv s.mem base SK 7 * mv s.mem base SS 7 ∧
        (∀ r, r ∉ W ++ colX → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
        Outside base Impl.X448.X86_64.ACC 112 s.mem t.mem := by
  rw [product, List.append_assoc, WP.block_append_iff]
  refine WP.mono (loads_ok hs SS W W_nodup (by decide) (by rw [W_len]; decide))
    fun s1 ⟨w1, v1, k1⟩ => ?_
  have hs1 := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (zeroAcc_ok s1) fun s2 ⟨z2, k2⟩ => ?_
  have hs2 := hs1.of_keeps k2 (by decide)
  have m2 : s2.mem = s.mem := k2.2.1.trans k1.2.1
  refine WP.mono (columns_ok hs2 (fun i => .mem (sc (SK + 8 * i)))
    w (fun i => word s2.mem base (SK + 8 * i)) Impl.X448.X86_64.mulCol
    (fun s' g _ wr out i hi => by
      have hsS : Scr s' base := ⟨(g _ rdi_colX).trans hs2.rdi, wr ▸ hs2.wr, hs2.nowrap⟩
      have := stable_sc hsS rdi_colX (d := SK + 8 * i) (by simp only [SK]; omega)
      rwa [out.word (by simp only [Impl.X448.X86_64.ACC, SK]; omega)
        (by simp only [SK]; omega)] at this)
    w_colX mulCol_hc mulCol_hw z2 (7 + 7) (Nat.le_refl _)) fun t ⟨gt, rdt, wrt, ot, et, _⟩ => ?_
  have hx : val7 (fun i => (word s2.mem base (SK + 8 * i)).toNat) = mv s.mem base SK 7 := by
    rw [m2, mv7]
  have hy : val7 (fun j => (s2.gpr (w j)).toNat) = mv s.mem base SS 7 := by
    rw [← rvW, show rv s2 W = rv s1 W from k2.rv_eq (by decide), v1, W_len]
  rw [mulCols_sum, hx, hy] at et
  have l1 := Proof.X448.X86_64.mv_lt s.mem base SK 7
  have l2 := Proof.X448.X86_64.mv_lt s.mem base SS 7
  have hl := prod_lt l1 l2
  have h0 : rv t (acc (7 + 7)) = 0 := by
    rcases Nat.eq_zero_or_pos (rv t (acc (7 + 7))) with h | h
    · exact h
    · exfalso
      have := Nat.mul_le_mul_left (2 ^ (64 * (7 + 7))) h
      generalize 2 ^ (64 * (7 + 7)) = Q at *
      omega
  have e2 : mv t.mem base Impl.X448.X86_64.ACC (7 + 7) =
      mv s.mem base SK 7 * mv s.mem base SS 7 := by
    rw [h0] at et
    generalize 2 ^ (64 * (7 + 7)) = Q at et
    generalize mv t.mem base Impl.X448.X86_64.ACC (7 + 7) = A at et ⊢
    omega
  refine ⟨e2, fun r hr => ?_, rdt.trans (k2.2.2.1.trans k1.2.2.1),
    wrt.trans (k2.2.2.2.trans k1.2.2.2), by rw [← m2]; exact ot⟩
  simp only [List.mem_append, not_or] at hr
  have sub : ∀ x ∈ [Reg.r15, .rcx, .rbp], x ∈ colX := by decide
  rw [gt r hr.2, k2.1 r (fun h => hr.2 (sub r h)), k1.1 r hr.1]

theorem word_ww {m : Mem} {base : Addr} {d e : Nat} (v : BitVec 64) (h : e + 8 ≤ d ∨ d + 8 ≤ e)
    (hd : d + 8 < 2 ^ 64) (he : e + 8 < 2 ^ 64) :
    word (m.writeW (off base d) v) base e = word m base e :=
  (writeW_outside m base v hd).word h he

/-- The arguments to `[r8 + OUT]` … `[r8 + ARG_S]`, and `r8` into `rdi`. -/
theorem args_ok {s : State} {base : Addr} (hb : s.gpr .r8 = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) :
    WP isa (.block saveArgs) s fun t =>
      word t.mem base OUT = s.gpr .rdi ∧ word t.mem base ARG_R = s.gpr .rsi ∧
      word t.mem base ARG_K = s.gpr .rdx ∧ word t.mem base ARG_S = s.gpr .rcx ∧
      Outside base OUT 32 s.mem t.mem ∧ t.gpr .rdi = base ∧
      (∀ r, r ≠ .rdi → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have w : ∀ d, d + 8 ≤ 8192 → InRegions s.wr (off base d) 8 :=
    fun d hd => ⟨_, hw, contains_sc hd⟩
  apply WP.of_runBlock
  simp only [saveArgs, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, ea_at, hb, State.store64,
    w OUT (by decide), w ARG_R (by decide), w ARG_K (by decide), w ARG_S (by decide), ite_true,
    RegUpd.gpr_setReg_self, RegUpd.mem_setReg, Option.map_some, Option.some.injEq,
    exists_eq_left']
  refine ⟨?_, ?_, ?_, ?_, ?_, trivial, fun r hr => by rw [RegUpd.gpr_setReg_of_ne _ _ hr], rfl, rfl⟩
  · rw [VG.Proof.Ed448.X86_64.word_ww _ (by decide) (by decide) (by decide), VG.Proof.Ed448.X86_64.word_ww _ (by decide) (by decide) (by decide),
      VG.Proof.Ed448.X86_64.word_ww _ (by decide) (by decide) (by decide), word_writeW_self]
  · rw [VG.Proof.Ed448.X86_64.word_ww _ (by decide) (by decide) (by decide), VG.Proof.Ed448.X86_64.word_ww _ (by decide) (by decide) (by decide),
      word_writeW_self]
  · rw [VG.Proof.Ed448.X86_64.word_ww _ (by decide) (by decide) (by decide), word_writeW_self]
  · rw [word_writeW_self]
  · exact (((writeW_outside _ _ _ (by decide)).mono (by decide) (by decide)).trans
      ((writeW_outside _ _ _ (by decide)).mono (by decide) (by decide))).trans
      (((writeW_outside _ _ _ (by decide)).mono (by decide) (by decide)).trans
      ((writeW_outside _ _ _ (by decide)).mono (by decide) (by decide)))

/-- `rsi` from a word of the working space. -/
theorem loadRsi_ok {s : State} {base : Addr} (hs : Scr s base) {d : Nat} (hd : d + 8 ≤ 8192) :
    WP isa (.block ([.mov .rsi (.mem (sc d))] : List Instr)) s fun t =>
      t.gpr .rsi = word s.mem base d ∧ Keeps [.rsi] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec,
    Proof.X448.X86_64.readSrc_sc hs hd, Option.map_some, RegUpd.gpr_setReg_self,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rw [RegUpd.gpr_setReg_of_ne _ _ hr]

/-- `r8–r14 += [SR]`, for a sum below `2^448`. -/
theorem addSR_ok {s : State} {base : Addr} (hs : Scr s base)
    (hlt : rem s + mv s.mem base SR 7 < 2 * L) :
    WP isa (.block (chain .add .adc W ((List.range 7).map fun i => .mem (sc (SR + 8 * i))))) s
      fun t => rem t = rem s + mv s.mem base SR 7 ∧ Keeps W s t := by
  have hc : chain .add .adc W ((List.range 7).map fun i => .mem (sc (SR + 8 * i))) =
      chain .add .adc (.r8 :: [.r9, .r10, .r11, .r12, .r13, .r14]) (.mem (sc 384) ::
        ([392, 400, 408, 416, 424, 432] : List Nat).map fun d => .mem (sc d)) := rfl
  rw [hc]
  refine WP.mono (Proof.X448.X86_64.add_chain_ok W s .r8 [.r9, .r10, .r11, .r12, .r13, .r14]
    (.mem (sc 384)) _ (word s.mem base 384)
    (([392, 400, 408, 416, 424, 432] : List Nat).map fun d => word s.mem base d)
    (fun _ h => h) W_nodup rfl (stable_sc hs (by decide) (by decide))
    (Proof.X448.X86_64.stable_scs hs (by decide) _ (by decide))) fun t ⟨c, _, et, kt⟩ => ?_
  have hv : wv (word s.mem base 384 :: ([392, 400, 408, 416, 424, 432] : List Nat).map
      fun d => word s.mem base d) = mv s.mem base SR 7 := rfl
  rw [hv, len7] at et
  refine ⟨?_, kt⟩
  have h2 : 2 * L < 2 ^ 448 := by decide +kernel
  have hc := Bool.toNat_le c
  show rv t (Reg.r8 :: [.r9, .r10, .r11, .r12, .r13, .r14]) =
    rv s (Reg.r8 :: [.r9, .r10, .r11, .r12, .r13, .r14]) + mv s.mem base SR 7
  change rv s (Reg.r8 :: [.r9, .r10, .r11, .r12, .r13, .r14]) + _ < _ at hlt
  generalize (2 : Nat) ^ 448 = M at et h2
  rcases Nat.lt_or_ge c.toNat 1 with h | h
  · have : c.toNat = 0 := by omega
    rw [this, Nat.mul_zero, Nat.add_zero] at et; exact et
  · have : M ≤ M * c.toNat := Nat.le_mul_of_pos_right _ h
    omega

/-- The loop over the product's words: `rsi = rdi + ACC`, a zero remainder and
`rbx = 112`. -/
theorem accInit_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block accInit) s fun t =>
      t.gpr .rsi = base + BitVec.ofNat 64 Impl.X448.X86_64.ACC ∧ rem t = 0 ∧
      t.gpr .rbx = BitVec.ofNat 64 112 ∧ Keeps (.rsi :: .rbx :: W) s t := by
  apply WP.of_runBlock
  simp only [accInit, zeroHigh, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32, execAlu, State.setReg32,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, ite_true, ite_false, reduceCtorEq,
      hs.rdi]
    rfl
  · simp only [rem, rv, W, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, ite_true, ite_false,
      reduceCtorEq]
    rfl
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, ite_true, ite_false, reduceCtorEq]
    rfl
  · simp only [W, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1,
      hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2,
      ite_false]

end VG.Proof.Ed448.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86_64.ScalarMulAddMain`. -/
section

/-!
# Ed448 scalar multiply-add on x86-64: the whole function

The contract the proof is written against (the facts of
`Spec.Ed448.scalarMulAddContract` it uses, stated for x86-64), and the
correctness of `vg_ed448_scalar_mul_add` against it.
-/

namespace VG.Proof.Ed448.X86_64

open VG VG.X86_64 VG.Impl.Ed448.X86_64
open VG.Proof.X448.X86_64 (Keeps Scr rv mv wv word off Outside ofs Saved saved_lt writeW_outside
  word_writeW_self contains_sc stores_ok W_len)
open VG.Impl.X448.X86_64 (W w sc at_ saved loads stores chain)
open VG.Spec.Ed448 (L bytesAt decodeLE)

/-- `vg_ed448_scalar_mul_add(out = rdi, r = rsi, k = rdx, s = rcx, scratch = r8)`. -/
def scalarMulAddLocal : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .rsi, 57⟩, ⟨s.gpr .rdx, 57⟩, ⟨s.gpr .rcx, 57⟩] ∧
    s.wr = [⟨s.gpr .rdi, 57⟩, ⟨s.gpr .r8, 8192⟩] ∧
    (⟨s.gpr .rsi, 57⟩ : Region).Disjoint ⟨s.gpr .r8, 8192⟩ ∧
    (⟨s.gpr .rdx, 57⟩ : Region).Disjoint ⟨s.gpr .r8, 8192⟩ ∧
    (⟨s.gpr .rcx, 57⟩ : Region).Disjoint ⟨s.gpr .r8, 8192⟩ ∧
    (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdi, 57⟩ ∧
    (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .r8, 8192⟩ ∧
    (⟨s.gpr .rdi, 57⟩ : Region).Disjoint ⟨s.gpr .r8, 8192⟩ ∧
    (s.gpr .r8).toNat + 8192 ≤ 2 ^ 64
  post s t := bytesAt t.mem (s.gpr .rdi) 57 = Spec.Ed448.scalarMulAdd
    (bytesAt s.mem (s.gpr .rsi) 57) (bytesAt s.mem (s.gpr .rdx) 57) (bytesAt s.mem (s.gpr .rcx) 57)
  pub s t := s.gpr .rsp = t.gpr .rsp ∧ s.gpr .rdi = t.gpr .rdi ∧ s.gpr .rsi = t.gpr .rsi ∧
    s.gpr .rdx = t.gpr .rdx ∧ s.gpr .rcx = t.gpr .rcx ∧ s.gpr .r8 = t.gpr .r8

theorem mulAdd_mod (r k s : Nat) :
    ((k % L * (s % L)) % L + r % L) % L = (r + k * s) % L := by
  rw [← Nat.mul_mod, Nat.add_comm r, Nat.add_mod (k * s)]

theorem decode_acc (m : Mem) (base : Addr) :
    decodeLE (bytesAt m (base + BitVec.ofNat 64 Impl.X448.X86_64.ACC) 112) =
      mv m base Impl.X448.X86_64.ACC 14 := by
  rw [decodeLE_eq]
  exact Proof.X448.X86_64.leNum_bytesAt_mv m base Impl.X448.X86_64.ACC 14

/-- A stores into the slot `o` (seven words) of the working space. -/
theorem storeSlot_ok {s : State} {base : Addr} (hs : Scr s base) (o : Nat) (ho : o + 56 ≤ 8192) :
    WP isa (.block (stores o W)) s fun t => mv t.mem base o 7 = rem s ∧ Outside base o 56 s.mem t.mem ∧
      (∀ r, t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr :=
  WP.mono (stores_ok hs o W (by rw [W_len]; omega)) fun t ⟨v, o', g, rd, wr⟩ =>
    ⟨by rw [W_len] at v; exact v, by rw [W_len] at o'; exact o', g, rd, wr⟩

theorem bytes_far {base p : Addr} {m m' : Mem} {n : Nat} (h : Outside base 0 8192 m m')
    (hp : ∀ i < n, 8192 ≤ ofs base (p + BitVec.ofNat 64 i)) : bytesAt m' p n = bytesAt m p n := by
  simp only [bytesAt]
  exact List.map_congr_left fun i hi => h _ (Or.inr (hp i (List.mem_range.mp hi)))

theorem scalarMulAdd_correct {s : State} (hp : scalarMulAddLocal.pre s) :
    WP isa scalarMulAdd s fun t => gprPreserved s t ∧ scalarMulAddLocal.post s t := by
  obtain ⟨hr, hw, hdr, hdk, hds, hro, hrs, hos, hn⟩ := hp
  obtain ⟨base, hbase⟩ : ∃ b, s.gpr .r8 = b := ⟨_, rfl⟩
  rw [hbase] at hdr hdk hds hrs hos hn
  have hws : (⟨base, 8192⟩ : Region) ∈ s.wr := by rw [hw, hbase]; simp
  have hwo : (⟨s.gpr .rdi, 57⟩ : Region) ∈ s.wr := by rw [hw]; simp
  have farR : ∀ i < 57, 8192 ≤ ofs base (s.gpr .rsi + BitVec.ofNat 64 i) :=
    fun i hi => VG.Proof.Ed448.X86_64.far hdr hi (by decide)
  have farK : ∀ i < 57, 8192 ≤ ofs base (s.gpr .rdx + BitVec.ofNat 64 i) :=
    fun i hi => VG.Proof.Ed448.X86_64.far hdk hi (by decide)
  have farS : ∀ i < 57, 8192 ≤ ofs base (s.gpr .rcx + BitVec.ofNat 64 i) :=
    fun i hi => VG.Proof.Ed448.X86_64.far hds hi (by decide)
  rw [scalarMulAdd]
  apply WP.seq
  rw [WP.block_append_iff]
  refine WP.mono (saveAt_ok .r8 hbase hws) fun s₁ ⟨g₁, rd₁, wr₁, o₁, sv₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86_64.args_ok (base := base) (by rw [g₁]; exact hbase) (by rw [wr₁]; exact hws))
    fun s₂ ⟨aO₂, aR₂, aK₂, aS₂, o₂, di₂, g₂, rd₂, wr₂⟩ => ?_
  have hs₂ : Scr s₂ base := ⟨di₂, by rw [wr₂, wr₁]; exact hws, by omega⟩
  rw [WP.block_append_iff]
  refine WP.mono (storeK_ok hs₂) fun s₃ ⟨k₃, o₃, g₃, rd₃, wr₃⟩ => ?_
  have hs₃ : Scr s₃ base := ⟨(g₃ _ (by decide)).trans di₂, wr₃ ▸ hs₂.wr, hs₂.nowrap⟩
  refine WP.mono (VG.Proof.Ed448.X86_64.loadRsi_ok hs₃ (d := ARG_K) (by decide)) fun s₄ ⟨rsi₄, k₄⟩ => ?_
  have hs₄ : Scr s₄ base := hs₃.of_keeps k₄ (by decide)
  have rd₄ : s₄.rd = s.rd := by rw [k₄.2.2.1, rd₃, rd₂, rd₁]
  have wr₄ : s₄.wr = s.wr := by rw [k₄.2.2.2, wr₃, wr₂, wr₁]
  have O₄ : Outside base 0 8192 s.mem s₄.mem := by
    rw [k₄.2.1]
    exact (o₁.mono (by decide) (by decide)).trans ((o₂.mono (by decide) (by decide)).trans
      (o₃.mono (by decide) (by decide)))
  have kp₄ : s₄.gpr .rsi = s.gpr .rdx := by
    rw [rsi₄, o₃.word (by decide) (by decide), aK₂, g₁]
  have hR₄ : (⟨s₄.gpr .rsi, 57⟩ : Region) ∈ s₄.rd ++ s₄.wr := by
    rw [kp₄, rd₄, hr]; simp
  -- k mod L
  apply WP.seq
  refine WP.mono (VG.Proof.Ed448.X86_64.reduce57_ok hs₄ (by rw [k₄.2.1]; exact k₃) hR₄ (by rw [kp₄]; exact farK))
    fun s₅ ⟨v₅, g₅, rd₅, wr₅, o₅⟩ => ?_
  have hs₅ : Scr s₅ base := ⟨(g₅ _ (by decide)).trans hs₄.rdi, wr₅ ▸ hs₄.wr, hs₄.nowrap⟩
  apply WP.seq
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86_64.storeSlot_ok hs₅ SK (by decide)) fun s₆ ⟨m₆, o₆, g₆, rd₆, wr₆⟩ => ?_
  have hs₆ : Scr s₆ base := ⟨(g₆ _).trans hs₅.rdi, wr₆ ▸ hs₅.wr, hs₅.nowrap⟩
  refine WP.mono (VG.Proof.Ed448.X86_64.loadRsi_ok hs₆ (d := ARG_S) (by decide)) fun s₇ ⟨rsi₇, k₇⟩ => ?_
  have hs₇ : Scr s₇ base := hs₆.of_keeps k₇ (by decide)
  have rd₇ : s₇.rd = s.rd := by rw [k₇.2.2.1, rd₆, rd₅, rd₄]
  have wr₇ : s₇.wr = s.wr := by rw [k₇.2.2.2, wr₆, wr₅, wr₄]
  have O₇ : Outside base 0 8192 s.mem s₇.mem := by
    rw [k₇.2.1]
    exact O₄.trans ((o₅.mono (by decide) (by decide)).trans (o₆.mono (by decide) (by decide)))
  have kp₇ : s₇.gpr .rsi = s.gpr .rcx := by
    rw [rsi₇, o₆.word (by decide) (by decide), o₅.word (by decide) (by decide), k₄.2.1,
      o₃.word (by decide) (by decide), aS₂, g₁]
  have hK₇ : mv s₇.mem base KC 7 = wv kWords := by
    rw [k₇.2.1, o₆.mv (by decide) (by decide), o₅.mv (by decide) (by decide), k₄.2.1, k₃]
  -- s mod L
  apply WP.seq
  refine WP.mono (VG.Proof.Ed448.X86_64.reduce57_ok hs₇ hK₇ (by rw [kp₇, rd₇, hr]; simp) (by rw [kp₇]; exact farS))
    fun s₈ ⟨v₈, g₈, rd₈, wr₈, o₈⟩ => ?_
  have hs₈ : Scr s₈ base := ⟨(g₈ _ (by decide)).trans hs₇.rdi, wr₈ ▸ hs₇.wr, hs₇.nowrap⟩
  apply WP.seq
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86_64.storeSlot_ok hs₈ SS (by decide)) fun s₉ ⟨m₉, o₉, g₉, rd₉, wr₉⟩ => ?_
  have hs₉ : Scr s₉ base := ⟨(g₉ _).trans hs₈.rdi, wr₉ ▸ hs₈.wr, hs₈.nowrap⟩
  refine WP.mono (VG.Proof.Ed448.X86_64.loadRsi_ok hs₉ (d := ARG_R) (by decide)) fun s₁₀ ⟨rsi₁₀, k₁₀⟩ => ?_
  have hs₁₀ : Scr s₁₀ base := hs₉.of_keeps k₁₀ (by decide)
  have rd₁₀ : s₁₀.rd = s.rd := by rw [k₁₀.2.2.1, rd₉, rd₈, rd₇]
  have wr₁₀ : s₁₀.wr = s.wr := by rw [k₁₀.2.2.2, wr₉, wr₈, wr₇]
  have O₁₀ : Outside base 0 8192 s.mem s₁₀.mem := by
    rw [k₁₀.2.1]
    exact O₇.trans ((o₈.mono (by decide) (by decide)).trans (o₉.mono (by decide) (by decide)))
  have kp₁₀ : s₁₀.gpr .rsi = s.gpr .rsi := by
    rw [rsi₁₀, o₉.word (by decide) (by decide), o₈.word (by decide) (by decide), k₇.2.1,
      o₆.word (by decide) (by decide), o₅.word (by decide) (by decide), k₄.2.1,
      o₃.word (by decide) (by decide), aR₂, g₁]
  have hK₁₀ : mv s₁₀.mem base KC 7 = wv kWords := by
    rw [k₁₀.2.1, o₉.mv (by decide) (by decide), o₈.mv (by decide) (by decide), hK₇]
  -- r mod L
  apply WP.seq
  refine WP.mono (VG.Proof.Ed448.X86_64.reduce57_ok hs₁₀ hK₁₀ (by rw [kp₁₀, rd₁₀, hr]; simp) (by rw [kp₁₀]; exact farR))
    fun s₁₁ ⟨v₁₁, g₁₁, rd₁₁, wr₁₁, o₁₁⟩ => ?_
  have hs₁₁ : Scr s₁₁ base := ⟨(g₁₁ _ (by decide)).trans hs₁₀.rdi, wr₁₁ ▸ hs₁₀.wr, hs₁₀.nowrap⟩
  -- The product.
  apply WP.seq
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86_64.storeSlot_ok hs₁₁ SR (by decide)) fun s₁₂ ⟨m₁₂, o₁₂, g₁₂, rd₁₂, wr₁₂⟩ => ?_
  have hs₁₂ : Scr s₁₂ base := ⟨(g₁₂ _).trans hs₁₁.rdi, wr₁₂ ▸ hs₁₁.wr, hs₁₁.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86_64.product_ok hs₁₂) fun s₁₃ ⟨e₁₃, g₁₃, rd₁₃, wr₁₃, o₁₃⟩ => ?_
  have hs₁₃ : Scr s₁₃ base := ⟨(g₁₃ _ (by decide)).trans hs₁₂.rdi, wr₁₃ ▸ hs₁₂.wr, hs₁₂.nowrap⟩
  refine WP.mono (VG.Proof.Ed448.X86_64.accInit_ok hs₁₃) fun s₁₄ ⟨rsi₁₄, v₁₄, b₁₄, k₁₄⟩ => ?_
  have hs₁₄ : Scr s₁₄ base := hs₁₃.of_keeps k₁₄ (by decide)
  have hK₁₄ : mv s₁₄.mem base KC 7 = wv kWords := by
    rw [k₁₄.2.1, o₁₃.mv (by decide) (by decide), o₁₂.mv (by decide) (by decide),
      o₁₁.mv (by decide) (by decide), hK₁₀]
  -- The product's words, reduced.
  apply WP.seq
  refine WP.mono (scalarLoop_ok hs₁₄ hK₁₄ (len := 112) (n₀ := 14) (by decide) (by decide)
    ⟨by decide, b₁₄, by rw [v₁₄]; rfl, fun _ _ => rfl, rfl, rfl, Outside.refl _ _ _ _⟩
    (fun k hk => by
      rw [rsi₁₄, Offset.add_add]
      exact ⟨_, List.mem_append_right _ hs₁₄.wr, contains_sc (by simp only [Impl.X448.X86_64.ACC]; omega)⟩)
    (fun i hi => Or.inr (by
      rw [rsi₁₄, Proof.X448.X86_64.ofs_off base (by simp only [Impl.X448.X86_64.ACC]; omega)]
      simp only [Impl.X448.X86_64.ACC, TMP]; omega)))
    fun s₁₅ ⟨v₁₅, g₁₅, rd₁₅, wr₁₅, o₁₅⟩ => ?_
  have hs₁₅ : Scr s₁₅ base := ⟨(g₁₅ _ (by decide)).trans hs₁₄.rdi, wr₁₅ ▸ hs₁₄.wr, hs₁₄.nowrap⟩
  -- The three reduced inputs.
  have eK : mv s₁₂.mem base SK 7 = decodeLE (bytesAt s.mem (s.gpr .rdx) 57) % L := by
    rw [o₁₂.mv (by decide) (by decide), o₁₁.mv (by decide) (by decide), k₁₀.2.1,
      o₉.mv (by decide) (by decide), o₈.mv (by decide) (by decide), k₇.2.1, m₆, v₅, kp₄,
      VG.Proof.Ed448.X86_64.bytes_far O₄ farK]
  have eS : mv s₁₂.mem base SS 7 = decodeLE (bytesAt s.mem (s.gpr .rcx) 57) % L := by
    rw [o₁₂.mv (by decide) (by decide), o₁₁.mv (by decide) (by decide), k₁₀.2.1, m₉, v₈, kp₇,
      VG.Proof.Ed448.X86_64.bytes_far O₇ farS]
  have eR : mv s₁₅.mem base SR 7 = decodeLE (bytesAt s.mem (s.gpr .rsi) 57) % L := by
    rw [o₁₅.mv (by decide) (by decide), k₁₄.2.1, o₁₃.mv (by decide) (by decide), m₁₂, v₁₁, kp₁₀,
      VG.Proof.Ed448.X86_64.bytes_far O₁₀ farR]
  have e₁₅ : rem s₁₅ = (decodeLE (bytesAt s.mem (s.gpr .rdx) 57) % L *
      (decodeLE (bytesAt s.mem (s.gpr .rcx) 57) % L)) % L := by
    rw [v₁₅, rsi₁₄, VG.Proof.Ed448.X86_64.decode_acc, k₁₄.2.1, e₁₃, eK, eS]
  have hL := L_pos
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86_64.addSR_ok hs₁₅ (by
    rw [e₁₅, eR]
    have := Nat.mod_lt (decodeLE (bytesAt s.mem (s.gpr .rsi) 57)) hL
    have := Nat.mod_lt (decodeLE (bytesAt s.mem (s.gpr .rdx) 57) % L *
      (decodeLE (bytesAt s.mem (s.gpr .rcx) 57) % L)) hL
    omega)) fun s₁₆ ⟨v₁₆, k₁₆⟩ => ?_
  have hs₁₆ : Scr s₁₆ base := hs₁₅.of_keeps k₁₆ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (csub_ok hs₁₆ (by
      rw [k₁₆.2.1, o₁₅.mv (by decide) (by decide)]; exact hK₁₄)
    (by
      rw [v₁₆, e₁₅, eR]
      have := Nat.mod_lt (decodeLE (bytesAt s.mem (s.gpr .rsi) 57)) hL
      have := Nat.mod_lt (decodeLE (bytesAt s.mem (s.gpr .rdx) 57) % L *
        (decodeLE (bytesAt s.mem (s.gpr .rcx) 57) % L)) hL
      omega)) fun s₁₇ ⟨v₁₇, g₁₇, rd₁₇, wr₁₇, o₁₇⟩ => ?_
  have hs₁₇ : Scr s₁₇ base := ⟨(g₁₇ _ (by decide)).trans hs₁₆.rdi, wr₁₇ ▸ hs₁₆.wr, hs₁₆.nowrap⟩
  have hout : word s₁₇.mem base OUT = s.gpr .rdi := by
    rw [o₁₇.word (by decide) (by decide), k₁₆.2.1, o₁₅.word (by decide) (by decide), k₁₄.2.1,
      o₁₃.word (by decide) (by decide), o₁₂.word (by decide) (by decide),
      o₁₁.word (by decide) (by decide), k₁₀.2.1, o₉.word (by decide) (by decide),
      o₈.word (by decide) (by decide), k₇.2.1, o₆.word (by decide) (by decide),
      o₅.word (by decide) (by decide), k₄.2.1, o₃.word (by decide) (by decide), aO₂, g₁]
  have sv : Saved base s.gpr s₁₇.mem := by
    have h₃ := (sv₁.outside o₂ (by decide)).outside o₃ (by decide)
    have h₄ : Saved base s.gpr s₄.mem := by rw [k₄.2.1]; exact h₃
    have h₆ := (h₄.outside o₅ (by decide)).outside o₆ (by decide)
    have h₇ : Saved base s.gpr s₇.mem := by rw [k₇.2.1]; exact h₆
    have h₉ := (h₇.outside o₈ (by decide)).outside o₉ (by decide)
    have h₁₀ : Saved base s.gpr s₁₀.mem := by rw [k₁₀.2.1]; exact h₉
    have h₁₃ := ((h₁₀.outside o₁₁ (by decide)).outside o₁₂ (by decide)).outside o₁₃ (by decide)
    have h₁₄ : Saved base s.gpr s₁₄.mem := by rw [k₁₄.2.1]; exact h₁₃
    have h₁₅ := h₁₄.outside o₁₅ (by decide)
    have h₁₆ : Saved base s.gpr s₁₆.mem := by rw [k₁₆.2.1]; exact h₁₅
    exact h₁₆.outside o₁₇ (by decide)
  have hlt : rem s₁₇ < L := by rw [v₁₇]; exact Nat.mod_lt _ hL
  have hwo₁₇ : (⟨s.gpr .rdi, 57⟩ : Region) ∈ s₁₇.wr := by
    rw [wr₁₇, k₁₆.2.2.2, wr₁₅, k₁₄.2.2.2, wr₁₃, wr₁₂, wr₁₁, wr₁₀]; exact hwo
  refine WP.mono (finish_ok hs₁₇ hout hwo₁₇ hos sv hlt) fun t ⟨bt, rt, gt, ft, _, _⟩ => ?_
  have O : Outside base 0 8192 s.mem s₁₇.mem := by
    have O₁₄ : Outside base 0 8192 s.mem s₁₄.mem := by
      rw [k₁₄.2.1]
      exact O₁₀.trans ((o₁₁.mono (by decide) (by decide)).trans ((o₁₂.mono (by decide)
        (by decide)).trans (o₁₃.mono (by decide) (by decide))))
    have O₁₆ : Outside base 0 8192 s.mem s₁₆.mem := by
      rw [k₁₆.2.1]; exact O₁₄.trans (o₁₅.mono (by decide) (by decide))
    exact O₁₆.trans (o₁₇.mono (by decide) (by decide))
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact rt (.rbx, 0) (by decide)
    · exact rt (.rbp, 8) (by decide)
    · rw [gt _ (by decide), g₁₇ _ (by decide), k₁₆.1 _ (by decide), g₁₅ _ (by decide),
        k₁₄.1 _ (by decide), g₁₃ _ (by decide), g₁₂, g₁₁ _ (by decide), k₁₀.1 _ (by decide), g₉,
        g₈ _ (by decide), k₇.1 _ (by decide), g₆, g₅ _ (by decide), k₄.1 _ (by decide),
        g₃ _ (by decide), g₂ _ (by decide), g₁]
    · exact rt (.r12, 16) (by decide)
    · exact rt (.r13, 24) (by decide)
    · exact rt (.r14, 32) (by decide)
    · exact rt (.r15, 40) (by decide)
  · have F : Frame [⟨base, 8192⟩, ⟨s.gpr .rdi, 57⟩] s.mem t.mem :=
      ((Outside.frame O).mono (by simp)).trans (ft.mono (by simp))
    exact F.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · exact hrs
      · exact hro) (by decide)
  · show bytesAt t.mem (s.gpr .rdi) 57 = _
    rw [bt, v₁₇, v₁₆, e₁₅, eR, Spec.Ed448.scalarMulAdd, VG.Proof.Ed448.X86_64.mulAdd_mod]

end VG.Proof.Ed448.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86_64.ScalarVerified`. -/
section

/-!
# Ed448 scalar arithmetic on x86-64: `Verified`

Correctness includes the ABI. Taint analysis checks that secret input bytes
never determine branches or memory addresses. A concrete witness proves the
signature contract is satisfiable.
-/

namespace VG.Proof.Ed448.X86_64

open VG VG.X86_64 VG.Impl.Ed448.X86_64

def scalarReduceSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x2000, 114⟩]
  wr := [⟨0x1000, 57⟩, ⟨0x3000, 8192⟩]

theorem scalarReduce_ok (s : State) (hs : scalarReduceLocal.pre s) :
    ∃ t s', Exec isa scalarReduce s t s' ∧ abiPreserved s s' ∧ scalarReduceLocal.post s s' := by
  obtain ⟨t, s', he, h⟩ := scalarReduce_correct hs
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he h.1, h.2⟩

/-- The arguments are public, and so is what the code stores in the working
space (writable region 1, at `rdx`): the output's address, at `OUT`. -/
def scalarReduceτ : X86_64.Taint.T :=
  { regs := .ofList [.rdi, .rsi, .rdx], flags := false, lens := [0, 8192], bases := [(.rdx, 1, 0)] }

theorem scalarReduce_agree {s₁ s₂ : State} (h₁ : scalarReduceLocal.pre s₁)
    (h₂ : scalarReduceLocal.pre s₂) (hpub : scalarReduceLocal.pub s₁ s₂) :
    X86_64.Taint.Agree VG.Proof.Ed448.X86_64.scalarReduceτ s₁ s₂ := by
  obtain ⟨-, p1, p2, p3⟩ := hpub
  have wf : ∀ s, scalarReduceLocal.pre s → X86_64.Taint.Wf VG.Proof.Ed448.X86_64.scalarReduceτ s := by
    intro s hs
    obtain ⟨-, hw, -, -, -, d, -⟩ := hs
    refine ⟨fun _ => ⟨by simp [hw, VG.Proof.Ed448.X86_64.scalarReduceτ], by simp [hw, d], by simp [hw]⟩, fun p hp => ?_⟩
    simp only [VG.Proof.Ed448.X86_64.scalarReduceτ, List.mem_cons, List.not_mem_nil, or_false] at hp
    subst hp; simp [X86_64.Taint.region, hw]
  refine ⟨⟨fun r hr => ?_, fun h => by cases h⟩, fun _ => ?_, wf _ h₁, wf _ h₂, ?_, ?_,
    X86_64.Taint.noLo⟩
  · simp only [VG.Proof.Ed448.X86_64.scalarReduceτ, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> assumption
  · rw [h₁.2.1, h₂.2.1, p1, p3]
  · intro sl h; simp [VG.Proof.Ed448.X86_64.scalarReduceτ] at h
  · intro sl h; simp [VG.Proof.Ed448.X86_64.scalarReduceτ] at h

theorem scalarReduce_ct :
    ConstantTime isa scalarReduceLocal.pre scalarReduceLocal.pub scalarReduce := by
  refine VG.Taint.constantTime (A := taint) VG.Proof.Ed448.X86_64.scalarReduceτ
    (fun _ _ h₁ h₂ hp => VG.Proof.Ed448.X86_64.scalarReduce_agree h₁ h₂ hp) (by taint_decide)

theorem scalarReduce_verified : Verified X86_64.target scalarReduce
    (Spec.Ed448.scalarReduceContract X86_64.abi) :=
  Verified.of_correct VG.Proof.Ed448.X86_64.scalarReduce_ok VG.Proof.Ed448.X86_64.scalarReduce_ct (by
    sig_implies [Spec.Ed448.scalarReduceContract, Spec.Ed448.scalarReduceSig,
      Spec.Ed448.scratchWords, X86_64.abi, X86_64.argRegs, scalarReduceLocal]
      [scalarReduceSat] using VG.Proof.Ed448.X86_64.scalarReduceSat)

def scalarMulAddSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rcx => 0x4000 | .r8 => 0x5000
    | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x2000, 57⟩, ⟨0x3000, 57⟩, ⟨0x4000, 57⟩]
  wr := [⟨0x1000, 57⟩, ⟨0x5000, 8192⟩]

theorem scalarMulAdd_ok (s : State) (hs : scalarMulAddLocal.pre s) :
    ∃ t s', Exec isa scalarMulAdd s t s' ∧ abiPreserved s s' ∧ scalarMulAddLocal.post s s' := by
  obtain ⟨t, s', he, h⟩ := VG.Proof.Ed448.X86_64.scalarMulAdd_correct hs
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he h.1, h.2⟩

/-- The arguments are public, and so is what the code stores in the working
space (writable region 1, at `r8`): the output's and inputs' addresses. -/
def scalarMulAddτ : X86_64.Taint.T :=
  { regs := .ofList [.rdi, .rsi, .rdx, .rcx, .r8], flags := false, lens := [0, 8192],
    bases := [(.r8, 1, 0)] }

theorem scalarMulAdd_agree {s₁ s₂ : State} (h₁ : scalarMulAddLocal.pre s₁)
    (h₂ : scalarMulAddLocal.pre s₂) (hpub : scalarMulAddLocal.pub s₁ s₂) :
    X86_64.Taint.Agree VG.Proof.Ed448.X86_64.scalarMulAddτ s₁ s₂ := by
  obtain ⟨-, p1, p2, p3, p4, p5⟩ := hpub
  have wf : ∀ s, scalarMulAddLocal.pre s → X86_64.Taint.Wf VG.Proof.Ed448.X86_64.scalarMulAddτ s := by
    intro s hs
    obtain ⟨-, hw, -, -, -, -, -, d, -⟩ := hs
    refine ⟨fun _ => ⟨by simp [hw, VG.Proof.Ed448.X86_64.scalarMulAddτ], by simp [hw, d], by simp [hw]⟩, fun p hp => ?_⟩
    simp only [VG.Proof.Ed448.X86_64.scalarMulAddτ, List.mem_cons, List.not_mem_nil, or_false] at hp
    subst hp; simp [X86_64.Taint.region, hw]
  refine ⟨⟨fun r hr => ?_, fun h => by cases h⟩, fun _ => ?_, wf _ h₁, wf _ h₂, ?_, ?_,
    X86_64.Taint.noLo⟩
  · simp only [VG.Proof.Ed448.X86_64.scalarMulAddτ, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> assumption
  · rw [h₁.2.1, h₂.2.1, p1, p5]
  · intro sl h; simp [VG.Proof.Ed448.X86_64.scalarMulAddτ] at h
  · intro sl h; simp [VG.Proof.Ed448.X86_64.scalarMulAddτ] at h

theorem scalarMulAdd_ct :
    ConstantTime isa scalarMulAddLocal.pre scalarMulAddLocal.pub scalarMulAdd := by
  refine VG.Taint.constantTime (A := taint) VG.Proof.Ed448.X86_64.scalarMulAddτ
    (fun _ _ h₁ h₂ hp => VG.Proof.Ed448.X86_64.scalarMulAdd_agree h₁ h₂ hp) (by taint_decide)

theorem scalarMulAdd_verified : Verified X86_64.target scalarMulAdd
    (Spec.Ed448.scalarMulAddContract X86_64.abi) :=
  Verified.of_correct VG.Proof.Ed448.X86_64.scalarMulAdd_ok VG.Proof.Ed448.X86_64.scalarMulAdd_ct (by
    sig_implies [Spec.Ed448.scalarMulAddContract, Spec.Ed448.scalarMulAddSig,
      Spec.Ed448.scratchWords, X86_64.abi, X86_64.argRegs, VG.Proof.Ed448.X86_64.scalarMulAddLocal]
      [scalarMulAddSat] using VG.Proof.Ed448.X86_64.scalarMulAddSat)

end VG.Proof.Ed448.X86_64

end
