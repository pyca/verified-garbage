import VerifiedGarbage.Proof.Weierstrass.Unch
import VerifiedGarbage.Impl.P256.EcdhSelect
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombSelectV

namespace VG.Proof.P256.EcdhJac.Select
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open VG.Impl.P256.EcdhSelect

/-- The loads of `k` pairs at `o + 16 i`. -/
theorem loads_ok (n : Nat) (loads : Nat → VReg) (hinj : ∀ i<n,∀ j<n,i≠j→loads i≠loads j) {s : State} {o : Nat}
    (ho : o + 16 * n ≤ 65536) (ho16 : o % 16 = 0)
    (hr : ∀ i < n, InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 (o + 16 * i)) 16) :
    ∀ k ≤ n, WP isa (.block ((List.range k).map fun i => Instr.ldrq (loads i) .x0 (o + 16 * i)))
      s fun t =>
      (∀ i < k, t.v (loads i) = s.mem.read (s.gpr .x0 + BitVec.ofNat 64 (o + 16 * i)) 16) ∧
      VKeep [] ((List.range k).map fun i => loads i) s t
  | 0, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), VKeep.refl _ _ _⟩
  | k + 1, hk => by
    simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil]
    rw [WP.block_append_iff]
    refine WP.mono (loads_ok n loads hinj ho ho16 hr k (by omega)) fun s₁ ⟨v₁, k₁⟩ => ?_
    refine wp_ldrq (by omega) (by rw [k₁.rd, k₁.wr, k₁.gpr _ List.not_mem_nil]; exact hr k (by omega))
      (WP.block_nil ⟨fun i hi => ?_, (k₁.mono (fun _ h => h) fun _ h => List.mem_append_left _ h).trans
        ((VKeep.setV _ _ _).mono (fun _ h => h) fun _ h => List.mem_append_right _ h)⟩)
    rcases Nat.lt_or_ge i k with h | h
    · rw [RegUpd.v_setV_of_ne _ _ (hinj i (by omega) k (by omega) (by omega)), v₁ i h]
    · obtain rfl : i = k := by omega
      rw [RegUpd.v_setV_self, k₁.mem, k₁.gpr _ List.not_mem_nil]

/-- `BIT` of `k` pairs into the accumulators, under the mask. -/
theorem selects_ok (n : Nat) (acc loads : Nat → VReg) (mask : VReg)
    (hinj : ∀ i<n,∀ j<n,i≠j→acc i≠acc j)
    (hal : ∀ i<n,∀ j<n,acc i≠loads j) (ham : ∀ i<n,acc i≠mask) {s : State} :
    ∀ k ≤ n, WP isa (.block ((List.range k).map fun i =>
        Instr.vop (.bsel .bit (acc i) (loads i) mask))) s fun t =>
      (∀ i < k, t.v (acc i) =
        VSelOp.bit.eval (s.v (acc i)) (s.v (loads i)) (s.v mask)) ∧
      VKeep [] ((List.range k).map fun i => acc i) s t
  | 0, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), VKeep.refl _ _ _⟩
  | k + 1, hk => by
    simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil]
    rw [WP.block_append_iff]
    refine WP.mono (selects_ok n acc loads mask hinj hal ham k (by omega)) fun s₁ ⟨v₁, k₁⟩ => ?_
    have e1 : s₁.v (acc k) = s.v (acc k) :=
      k₁.v _ (not_mem_map_range fun i hi => hinj i (by omega) k (by omega) (by omega))
    have e2 : s₁.v (loads k) = s.v (loads k) :=
      k₁.v _ (not_mem_map_range fun i hi => hal i (by omega) k (by omega))
    have e3 : s₁.v mask = s.v mask :=
      k₁.v _ (not_mem_map_range fun i hi e => ham i (by omega) e)
    refine wp_vop (d := acc k) (x := VSelOp.bit.eval (s.v (acc k)) (s.v (loads k)) (s.v mask))
      (by simp only [VOp.eval, e1, e2, e3]) (WP.block_nil ⟨fun i hi => ?_,
        (k₁.mono (fun _ h => h) fun _ h => List.mem_append_left _ h).trans
        ((VKeep.setV _ _ _).mono (fun _ h => h) fun _ h => List.mem_append_right _ h)⟩)
    rcases Nat.lt_or_ge i k with h | h
    · rw [RegUpd.v_setV_of_ne _ _ (hinj i (by omega) k (by omega) (by omega)), v₁ i h]
    · obtain rfl : i = k := by omega
      rw [RegUpd.v_setV_self]


abbrev acc (i : Nat) := vectorAcc.getD i .v0
abbrev load (i : Nat) := vectorLoad.getD i .v18
def written : List VReg := [.v28,.v29]++vectorLoad++vectorAcc

theorem acc_inj : ∀ i<10,∀ j<10,i≠j→acc i≠acc j := by decide
theorem load_inj : ∀ i<10,∀ j<10,i≠j→load i≠load j := by decide
theorem acc_load : ∀ i<10,∀ j<10,acc i≠load j := by decide
theorem acc_mask : ∀ i<10,acc i≠.v29 := by decide
theorem acc_idx : ∀ i<10,acc i≠.v28 := by decide
theorem load_mask : ∀ i<10,load i≠.v29 := by decide
theorem load_idx : ∀ i<10,load i≠.v28 := by decide
theorem acc_mem : ∀ i<10,acc i∈vectorAcc := by decide
theorem load_mem : ∀ i<10,load i∈vectorLoad := by decide

def row (tbl r : Nat) : List Instr :=
  [.vop (.add .d2 .v28 .v28 .v31),.vop (.cmeq .d2 .v29 .v28 .v30)] ++
  (List.range 10).map (fun i => .ldrq (load i) .x0 (tbl+160*r+16*i)) ++
  (List.range 10).map (fun i => .vop (.bsel .bit (acc i) (load i) .v29))

theorem row_ok {s : State} {tbl r a : Nat} (ha : a<2^64) (hr : r+1<2^64)
    (hidx : s.v .v28=dup2 (BitVec.ofNat 64 r))
    (hinc : s.v .v31=dup2 1) (hmag : s.v .v30=dup2 (BitVec.ofNat 64 a))
    (hbound : tbl+160*r+160≤65536) (halign : tbl%16=0)
    (hread : ∀ i<10,InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 (tbl+160*r+16*i)) 16) :
    WP isa (.block (row tbl r)) s fun t =>
      t.v .v28=dup2 (BitVec.ofNat 64 (r+1)) ∧
      (∀ i<10,t.v (acc i)=if a=r+1 then
        s.mem.read (s.gpr .x0+BitVec.ofNat 64 (tbl+160*r+16*i)) 16 else s.v (acc i)) ∧
      VKeep [] written s t := by
  simp only [row, List.cons_append, List.nil_append]
  refine wp_vop (d:=.v28) (x:=dup2 (BitVec.ofNat 64 (r+1)))
    (by simp only [VOp.eval,hidx,hinc,map2_dup2,BitVec.ofNat_add]; rfl) ?_
  refine wp_vop (d:=.v29) (x:=if a=r+1 then BitVec.allOnes 128 else 0)
    (by simp only [VOp.eval,RegUpd.v_setV_self,
      RegUpd.v_setV_of_ne _ _ (by decide : VReg.v30≠.v28),hmag,cmeq_dup2,ofNat_eq_iff ha hr]) ?_
  rw [WP.block_append_iff]
  refine WP.mono (loads_ok 10 load load_inj (o:=tbl+160*r)
    (s:=(s.setV .v28 (dup2 (BitVec.ofNat 64 (r+1)))).setV .v29 (if a=r+1 then BitVec.allOnes 128 else 0))
    (by omega) (by omega) (fun i hi=>hread i hi) 10 (by omega)) fun s₃ ⟨l₃,k₃⟩ => ?_
  refine WP.mono (selects_ok 10 acc load .v29 acc_inj acc_load acc_mask (s:=s₃) 10 (by omega))
    fun t ⟨b₄,k₄⟩ => ?_
  refine ⟨?_,fun i hi=>?_,?_⟩
  · rw [k₄.v _ (not_mem_map_range acc_idx),k₃.v _ (not_mem_map_range load_idx),
      RegUpd.v_setV_of_ne _ _ (by decide : VReg.v28≠.v29),RegUpd.v_setV_self]
  · have hm₃ : s₃.v .v29=if a=r+1 then BitVec.allOnes 128 else 0 := by
      rw [k₃.v _ (not_mem_map_range load_mask),RegUpd.v_setV_self]
    have hac : s₃.v (acc i)=s.v (acc i) := by
      rw [k₃.v _ (not_mem_map_range fun j hj => Ne.symm (acc_load i hi j hj)),
        RegUpd.v_setV_of_ne _ _ (acc_mask i hi),RegUpd.v_setV_of_ne _ _ (acc_idx i hi)]
    rw [b₄ i hi,hac,l₃ i hi,hm₃,bit_mask]
    rfl
  · have hloads : ∀ i<10,load i∈written := fun i hi=>by
      simp only [written,List.mem_append,List.mem_cons]
      exact Or.inl (Or.inr (load_mem i hi))
    have haccs : ∀ i<10,acc i∈written := fun i hi=>by
      simp only [written,List.mem_append]
      exact Or.inr (acc_mem i hi)
    exact ((((VKeep.setV _ _ _).mono (fun _ h=>h) (by simp [written])).trans
      ((VKeep.setV _ _ _).mono (fun _ h=>h) (by simp [written]))).trans
      (k₃.mono (fun _ h=>h) (map_range_sub hloads))).trans
      (k₄.mono (fun _ h=>h) (map_range_sub haccs))

theorem v30_not_written : VReg.v30∉written := by decide
theorem v31_not_written : VReg.v31∉written := by decide

def scan (tbl k : Nat) := (List.range k).flatMap (row tbl)
abbrev picked (s : State) (tbl a i : Nat) : BitVec 128 :=
  s.mem.read (s.gpr .x0+BitVec.ofNat 64 (tbl+160*(a-1)+16*i)) 16

theorem scan_ok {s : State} {tbl a : Nat} (ha : a<2^64)
    (hidx : s.v .v28=dup2 0) (hinc : s.v .v31=dup2 1)
    (hmag : s.v .v30=dup2 (BitVec.ofNat 64 a)) (hz : ∀ i<10,s.v (acc i)=0)
    (hbound : tbl+2560≤65536) (halign : tbl%16=0)
    (hread : ∀ r<16,∀ i<10,InRegions (s.rd++s.wr)
      (s.gpr .x0+BitVec.ofNat 64 (tbl+160*r+16*i)) 16) :
    ∀ k≤16,WP isa (.block (scan tbl k)) s fun t=>
      t.v .v28=dup2 (BitVec.ofNat 64 k) ∧
      (∀ i<10,t.v (acc i)=if 0<a ∧ a≤k then picked s tbl a i else 0) ∧
      VKeep [] written s t
  | 0,_ => WP.block_nil ⟨hidx,fun i hi=>by rw [ite_eq_right (by omega)]; exact hz i hi,VKeep.refl _ _ _⟩
  | k+1,hk => by
    simp only [scan,List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil]
    rw [WP.block_append_iff]
    refine WP.mono (scan_ok ha hidx hinc hmag hz hbound halign hread k (by omega))
      fun s₁ ⟨idx₁,acc₁,keep₁⟩=>?_
    refine WP.mono (row_ok ha (by omega) idx₁
      ((keep₁.v _ v31_not_written).trans hinc) ((keep₁.v _ v30_not_written).trans hmag)
      (by omega) halign (fun i hi=>by
        rw [keep₁.rd,keep₁.wr,keep₁.gpr _ List.not_mem_nil]
        exact hread k (by omega) i hi)) fun t ⟨idx₂,acc₂,keep₂⟩=>?_
    refine ⟨idx₂,fun i hi=>?_,keep₁.trans keep₂⟩
    rw [acc₂ i hi,keep₁.mem,keep₁.gpr _ List.not_mem_nil,acc₁ i hi]
    by_cases h : a=k+1
    · subst a
      simp only [ite_true,show 0<k+1 ∧ k+1≤k+1 by omega]
      rfl
    · rw [ite_eq_right h]
      have he : (0<a ∧ a≤k)↔(0<a ∧ a≤k+1) := by omega
      simp only [he]

/-- Stores of `k` vector registers `f i` at `o + 16 i` of the working space. -/
theorem storesReg_ok {size : Nat} (f : Nat → VReg) (reg : Reg) {s : State} {base : Addr} {o : Nat}
    (hs : Scr s base size) (hreg : s.gpr reg=off base o) : ∀ k, o + 16 * k ≤ size →
    WP isa (.block ((List.range k).map fun i => Instr.strq (f i) reg (16 * i))) s fun t =>
      (∀ j < 2 * k, word t.mem base (o + 8 * j) = vdword (s.v (f (j / 2))) (j % 2)) ∧
      KeepRegs [] s t ∧ t.v = s.v ∧ Outside base o (16 * k) s.mem t.mem
  | 0, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), ⟨fun _ _ => rfl, rfl, rfl, rfl⟩, rfl,
      Outside.refl _ _ _ _⟩
  | k + 1, hk => by
    have hn := hs.nowrap
    have he := hs.enc
    simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil]
    rw [WP.block_append_iff]
    refine WP.mono (storesReg_ok f reg hs hreg k (by omega)) fun s₁ ⟨w₁, k₁, v₁, O₁⟩ => ?_
    have hx0 : s₁.gpr reg = off base o := by rw [k₁.gpr _ List.not_mem_nil,hreg]
    have haddr : s₁.gpr reg+BitVec.ofNat 64 (16*k)=off base (o+16*k) := by
      rw [hx0]; exact (BitVec.add_assoc _ _ _).trans (congrArg (base + ·) (BitVec.ofNat_add_ofNat ..))
    refine wp_strq (by omega) (by rw [haddr, k₁.wr]; exact ⟨_, hs.wr, hs.contains (by omega) (by decide)⟩) ?_
    rw [haddr, v₁, ← ofVDwords_vdword (s.v (f k)), write16_dwords, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    have Oa := writeW_outside s₁.mem base (d := o + 16 * k) (vdword (s.v (f k)) 0) (by omega)
    have Ob := writeW_outside (s₁.mem.writeW (off base (o + 16 * k)) (vdword (s.v (f k)) 0)) base
      (d := o + 16 * k + 8) (vdword (s.v (f k)) 1) (by omega)
    refine ⟨fun j hj => ?_, k₁.trans ⟨fun _ _ => rfl, rfl, rfl, rfl⟩, rfl, ?_⟩
    · rcases Nat.lt_or_ge j (2 * k) with h | h
      · rw [Ob.word (by omega) (by omega), Oa.word (by omega) (by omega), w₁ j h]
      · rcases Nat.lt_or_ge j (2 * k + 1) with h' | h'
        · obtain rfl : j = 2 * k := by omega
          rw [Ob.word (by omega) (by omega), show o + 8 * (2 * k) = o + 16 * k by omega, word_writeW_self,
            show 2 * k / 2 = k by omega, show 2 * k % 2 = 0 by omega]
        · obtain rfl : j = 2 * k + 1 := by omega
          rw [show o + 8 * (2 * k + 1) = o + 16 * k + 8 by omega, word_writeW_self,
            show (2 * k + 1) / 2 = k by omega, show (2 * k + 1) % 2 = 1 by omega]
    · exact (O₁.mono (Nat.le_refl _) (by omega)).trans
        ((Oa.mono (by omega) (by omega)).trans (Ob.mono (by omega) (by omega)))


def setup : List Instr :=
  [.movz .x .x5 1 0,.vop (.dup .d2 .v31 .x5),.vop (.dup .d2 .v30 .x2),.vop (.movi0 .v28)] ++
  vectorAcc.map (fun r=>.vop (.movi0 r))
def allWritten := [.v30,.v31]++written

theorem setup_ok (s : State) : WP isa (.block setup) s fun t=>
    t.v .v28=dup2 0 ∧ t.v .v31=dup2 1 ∧ t.v .v30=dup2 (s.gpr .x2) ∧
    (∀ i<10,t.v (acc i)=0) ∧ VKeep [.x5] allWritten s t := by
  let u := (((s.write .x .x5 1).setV .v31 (dup2 1)).setV .v30 (dup2 (s.gpr .x2))).setV .v28 0
  have hpre : WP isa (.block [.movz .x .x5 1 0,.vop (.dup .d2 .v31 .x5),
      .vop (.dup .d2 .v30 .x2),.vop (.movi0 .v28)]) s (·=u) := by
    apply WP.of_runBlock
    simp only [runBlock_cons,exec,show 16*0<Size.x.bits from by decide,ite_true,
      VOp.eval,RegUpd.gpr_write_self,RegUpd.gpr_setV,RegUpd.gpr_write_of_ne _ _ _ (by decide : Reg.x2≠.x5),
      Option.map_some,runStep_some,runBlock_nil,Option.some.injEq,exists_eq_left']
    rfl
  have hku : VKeep [.x5] [.v31,.v30,.v28] s u := by
    refine ⟨fun r hr=>?_,rfl,rfl,rfl,rfl,fun r hr=>?_⟩
    · exact RegUpd.gpr_write_of_ne _ _ _ (by simpa using hr)
    · simp only [u,RegUpd.v_setV_of_ne _ _ (by simp_all : r≠.v28),
        RegUpd.v_setV_of_ne _ _ (by simp_all : r≠.v30),
        RegUpd.v_setV_of_ne _ _ (by simp_all : r≠.v31)]
      rfl
  rw [setup,WP.block_append_iff]
  refine WP.mono hpre fun u₁ hu=>?_
  subst u₁
  refine WP.mono (movisV_ok u vectorAcc) fun t ⟨hz,hk⟩=>?_
  refine ⟨?_,?_,?_,fun i hi=>hz _ (acc_mem i hi),?_⟩
  · rw [hk.v _ (by decide : VReg.v28∉vectorAcc)]
    exact dup2_zero.symm
  · rw [hk.v _ (by decide : VReg.v31∉vectorAcc)]
    rfl
  · rw [hk.v _ (by decide : VReg.v30∉vectorAcc)]
    rfl
  · exact (hku.mono (fun _ h=>h) (by decide)).trans
      (hk.mono (by simp) (by decide))

theorem cachePtr_ok (s : State) :
    WP isa (.block [.movz .x .x17 5400 0,.add .x .x17 .x0 .x17]) s fun t=>
      t.gpr .x17=off (s.gpr .x0) 5400 ∧ VKeep [.x17] [] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,exec,show 16*0<Size.x.bits from by decide,ite_true,read_x,
    RegUpd.gpr_write_self,RegUpd.gpr_write_of_ne _ _ _ (by decide : Reg.x0≠.x17),
    BitVec.setWidth_eq,runStep_some,runBlock_nil,Option.some.injEq,exists_eq_left']
  refine ⟨rfl,⟨fun r hr=>?_,rfl,rfl,rfl,rfl,fun _ _=>rfl⟩⟩
  have hn : r≠.x17 := by simpa using hr
  rw [RegUpd.gpr_write_of_ne _ _ _ hn,RegUpd.gpr_write_of_ne _ _ _ hn]

def output (j : Nat) := if j<12 then 704+8*j else 5400+8*(j-12)
def outputRanges : List (Nat×Nat) := [(704,96),(5400,64)]
def store : List Instr :=
  (List.range 6).map (fun i=>.strq (acc i) .x0 (704+16*i)) ++
  [.movz .x .x17 5400 0,.add .x .x17 .x0 .x17] ++
  (List.range 4).map (fun i=>.strq (acc (i+6)) .x17 (16*i))

theorem stores_ok {s : State} {base : Addr} (hs : Scr s base 8192) :
    WP isa (.block store) s fun t=>
      (∀ j<20,word t.mem base (output j)=vdword (s.v (acc (j/2))) (j%2)) ∧
      KeepRegs [.x17] s t ∧ Unch base outputRanges s.mem t.mem := by
  rw [store,WP.block_append_iff,WP.block_append_iff]
  refine WP.mono (qstoresV_ok acc hs (by decide : 704%16=0) 6 (by decide))
    fun s₁ ⟨w₁,k₁,v₁,o₁⟩=>?_
  refine WP.mono (cachePtr_ok s₁) fun s₂ ⟨p₂,k₂⟩=>?_
  have hs₂ : Scr s₂ base 8192 := by
    refine ⟨?_,?_,?_,hs.enc⟩
    · rw [k₂.gpr _ (by decide),k₁.gpr _ List.not_mem_nil,hs.x0]
    · simpa only [k₂.wr,k₁.wr] using hs.wr
    · exact hs.nowrap
  have hptr : s₂.gpr .x17=off base 5400 := by
    rw [p₂,k₁.gpr _ List.not_mem_nil,hs.x0]
  refine WP.mono (storesReg_ok (fun i=>acc (i+6)) .x17 hs₂ hptr 4 (by decide))
    fun t ⟨w₃,k₃,v₃,o₃⟩=>?_
  refine ⟨fun j hj=>?_,?_,?_⟩
  · by_cases h : j<12
    · rw [output,ite_eq_left h,o₃.word (by omega) (by omega),k₂.mem,w₁ j h]
    · have hw := w₃ (j-12) (by omega)
      have he : (j-12)/2+6=j/2 := by omega
      have hr : (j-12)%2=j%2 := by omega
      simpa only [output,ite_eq_right h,he,hr,k₂.v _ List.not_mem_nil,v₁] using hw
  · exact ((k₁.mono (by simp)).trans (VG.Proof.Mont.AArch64.Keeps.regs k₂.keeps)).trans (k₃.mono (by simp))
  · have om : Unch base [(704,96)] s.mem s₂.mem := by
      rw [k₂.mem]; exact o₁.unch
    exact om.trans o₃.unch

theorem neon_split : neon 2816 704 5400=setup++scan 2816 16++store := by
  simp only [neon,setup,scan,store,List.append_assoc]
  dsimp only [row,acc,load]
  rfl

theorem neon_ok {s : State} {base : Addr} {a : Nat} (hs : Scr s base 8192)
    (ha : a≤16) (hmag : s.gpr .x2=BitVec.ofNat 64 a) :
    WP isa (.block (neon 2816 704 5400)) s fun t=>
      (∀ j<20,word t.mem base (output j)=if a=0 then 0 else
        word s.mem base (2816+160*(a-1)+8*j)) ∧
      KeepRegs [.x5,.x17] s t ∧ Unch base outputRanges s.mem t.mem := by
  rw [neon_split]
  rw [WP.block_append_iff,WP.block_append_iff]
  refine WP.mono (setup_ok s) fun s₁ ⟨idx₁,inc₁,mag₁,z₁,k₁⟩=>?_
  have hs₁ : Scr s₁ base 8192 := ⟨(k₁.gpr _ (by decide)).trans hs.x0,
    by simpa only [k₁.wr] using hs.wr,hs.nowrap,hs.enc⟩
  refine WP.mono (scan_ok (by omega) idx₁ inc₁ (mag₁.trans (congrArg dup2 hmag)) z₁
    (by decide : 2816+2560≤65536) (by decide)
    (fun r hr i hi=>by
      rw [hs₁.x0]
      exact ⟨_,List.mem_append_right _ hs₁.wr,hs₁.contains (by omega) (by decide)⟩)
    16 (by decide)) fun s₂ ⟨_,acc₂,k₂⟩=>?_
  have hs₂ : Scr s₂ base 8192 := ⟨(k₂.gpr _ List.not_mem_nil).trans hs₁.x0,
    by simpa only [k₂.wr] using hs₁.wr,hs.nowrap,hs.enc⟩
  refine WP.mono (stores_ok hs₂) fun t ⟨wt,kt,ot⟩=>?_
  refine ⟨fun j hj=>?_,?_,?_⟩
  · rw [wt j hj,acc₂ (j/2) (by omega)]
    by_cases hz : a=0
    · simp only [hz,Nat.lt_irrefl,false_and,ite_false,ite_true,vdword_zero]
    · rw [ite_eq_left (by omega : 0<a ∧ a≤16),ite_eq_right hz]
      unfold picked
      rw [k₁.mem,hs₁.x0,vdword_read16 _ _ (by omega : j%2<2),BitVec.add_assoc,BitVec.ofNat_add_ofNat]
      rw [show 2816+160*(a-1)+16*(j/2)+8*(j%2)=2816+160*(a-1)+8*j by omega]
  · exact (((VG.Proof.Mont.AArch64.Keeps.regs k₁.keeps).mono (by simp)).trans
      ((VG.Proof.Mont.AArch64.Keeps.regs k₂.keeps).mono (by simp))).trans
      (kt.mono (by simp))
  · simpa only [k₂.mem,k₁.mem] using ot

end VG.Proof.P256.EcdhJac.Select
