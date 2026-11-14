module

public import VerifiedGarbage.Proof.Sm4.AArch64.Serial.Prepared
public import VerifiedGarbage.Proof.Sm4.AArch64.Serial.Load
public import VerifiedGarbage.Proof.Sm4.AArch64.Serial.Round
import VerifiedGarbage.Proof.Sm4.Layout
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
import VerifiedGarbage.Proof.Framework.Interleave
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
public import VerifiedGarbage.Spec.Aes
import VerifiedGarbage.Proof.Sm4.CtrCipher
import VerifiedGarbage.Proof.Framework.CallLay
public import VerifiedGarbage.Proof.Sm4.AArch64.ModeCore
public import VerifiedGarbage.Proof.Sm4.AArch64.Serial.State
public import VerifiedGarbage.Spec.Sm4.Ctr
import VerifiedGarbage.Proof.Modes.AArch64.Fb
import VerifiedGarbage.Proof.Sm4.AArch64.Lit
public import VerifiedGarbage.Proof.Sm4.AArch64.PreparedBody

/-! ### `Sm4.AArch64.Serial.Crypt`, which only this module used -/

section

/-! ### `Sm4.AArch64.Serial.Block`, which only this module used -/

section

/-! # Load and store a single SM4 block in big-endian word order -/

@[expose] public section

namespace VG.Proof.Sm4.AArch64.Serial

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Sm4.AArch64.Serial

theorem wordReg_ne_base : ∀ j < 4, wordReg j ≠ .x5 := by decide

theorem readBE_word (m : Mem) (p : Addr) (i : Nat) (hi : i < 4) :
    rev32 (m.readW (p + BitVec.ofNat 64 (4*i)) 32) =
      Spec.Sm4.wordAt (Spec.Sm4.blockAt m p) (4*i) := by
  rw [rev32_readW,Spec.Sm4.wordAt]
  rw [VG.Proof.Sm4.blockAt_getD _ _ (by omega_using [hi]),VG.Proof.Sm4.blockAt_getD _ _ (by omega_using [hi]),
    VG.Proof.Sm4.blockAt_getD _ _ (by omega_using [hi]),VG.Proof.Sm4.blockAt_getD _ _ (by omega_using [hi])]
  have add1 (j : Nat) : p + BitVec.ofNat 64 (j+1) = p + BitVec.ofNat 64 j + 1 := by
    rw [BitVec.ofNat_add,BitVec.add_assoc]; rfl
  simp only [show 4*i+2 = (4*i+1)+1 by omega_using [],
    show 4*i+3 = ((4*i+1)+1)+1 by omega_using [],add1]

theorem loadWord_run {s : State} {r : Reg} {i : Nat} (hi : i < 4)
    (hread : InRegions (s.rd ++ s.wr) (s.gpr .x5 + BitVec.ofNat 64 (768+4*i)) 4) :
    ∃ t, runBlock isa [.ldr .w r .x5 (768+4*i),.rev32 r r] s = some t ∧
      (t.gpr r).setWidth 32 = rev32 (s.mem.readW (s.gpr .x5 + BitVec.ofNat 64 (768+4*i)) 32) ∧
      (∀ q, q ≠ r → t.gpr q = s.gpr q) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.v = s.v := by
  let a := s.write .w r (s.mem.readW (s.gpr .x5 + BitVec.ofNat 64 (768+4*i)) 32)
  let b := a.write .w r (rev32 (a.read .w r))
  refine ⟨b,?_,?_,?_,rfl,rfl,rfl,rfl,rfl⟩
  · rw [runBlock_cons,exec_ldr_w ⟨by omega_using [],by omega_using [hi]⟩ hread,runStep_some,
      runBlock_cons,exec_rev32,runStep_some,runBlock_nil]
  · simp only [b,a,gpr_write_self,State.read,Size.bits,
      BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64),BitVec.setWidth_eq]
  · intro q hq
    simp only [b,a,gpr_write_of_ne _ _ _ hq]

theorem loads_run (s : State) (n : Nat) (hn : n ≤ 4)
    (hread : ∀ i < 4, InRegions (s.rd ++ s.wr) (s.gpr .x5 + BitVec.ofNat 64 (768+4*i)) 4) :
    ∃ t, runBlock isa ((List.range n).flatMap fun i =>
        [.ldr .w (wordReg i) .x5 (768+4*i),.rev32 (wordReg i) (wordReg i)]) s = some t ∧
      (∀ j < n, words t j = rev32 (s.mem.readW (s.gpr .x5 + BitVec.ofNat 64 (768+4*j)) 32)) ∧
      (∀ r, (∀ j < n, r ≠ wordReg j) → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.v = s.v := by
  induction n with
  | zero => exact ⟨s,rfl,fun _ h => absurd h (by omega_using []),fun _ _ => rfl,rfl,rfl,rfl,rfl,rfl⟩
  | succ n ih =>
    obtain ⟨a,ae,aw,ag,am,ard,awr,asp,avec⟩ := ih (by omega_using [hn])
    have ab : a.gpr .x5 = s.gpr .x5 := ag _ (fun j hj => (wordReg_ne_base j (by omega_using [hn, hj])).symm)
    have ar : InRegions (a.rd ++ a.wr) (a.gpr .x5 + BitVec.ofNat 64 (768+4*n)) 4 := by
      rw [ard,awr,ab]
      exact hread n (by omega_using [hn])
    obtain ⟨b,be,bv,bg,bm,brd,bwr,bsp,bvec⟩ := loadWord_run (r := wordReg n) (by omega_using [hn]) ar
    refine ⟨b,?_,?_,?_,bm.trans am,brd.trans ard,bwr.trans awr,bsp.trans asp,bvec.trans avec⟩
    · rw [List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,
        VG.Interleave.runBlock_append,ae,Option.bind_some,be]
    · intro j hj
      by_cases h : j = n
      · subst j
        simpa only [words,am,ab] using bv
      · rw [words,bg _ (fun e => h (wordReg_inj _ (by omega_using [hn, hj]) _ (by omega_using [hn]) e))]
        exact aw j (by omega_using [hj, h])
    · intro r hr
      exact (bg r (hr n (by omega_using []))).trans (ag r (fun j hj => hr j (by omega_using [hj])))

theorem storeWord_run {s : State} {r : Reg} {i : Nat} (hr : r ≠ .x5) (hi : i < 4)
    (hwrite : InRegions s.wr (s.gpr .x5 + BitVec.ofNat 64 (768+4*i)) 4) :
    ∃ t, runBlock isa [.rev32 r r,.str .w r .x5 (768+4*i)] s = some t ∧
      t.mem = s.mem.writeW (s.gpr .x5 + BitVec.ofNat 64 (768+4*i)) (rev32 ((s.gpr r).setWidth 32)) ∧
      (∀ q, q ≠ r → t.gpr q = s.gpr q) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.v = s.v := by
  let a := s.write .w r (rev32 ((s.gpr r).setWidth 32))
  let t := { a with mem := a.mem.writeW (a.gpr .x5 + BitVec.ofNat 64 (768+4*i)) ((a.gpr r).setWidth 32) }
  have base : a.gpr .x5 = s.gpr .x5 := gpr_write_of_ne _ _ _ hr.symm
  refine ⟨t,?_,?_,?_,rfl,rfl,rfl,rfl⟩
  · rw [runBlock_cons,exec_rev32,runStep_some,runBlock_cons]
    rw [exec_str_w ⟨by omega_using [],by omega_using [hi]⟩ (by
      change InRegions a.wr (a.gpr .x5 + BitVec.ofNat 64 (768+4*i)) 4
      rw [base]; exact hwrite),runStep_some,runBlock_nil]
    rfl
  · simp only [t,a,base,gpr_write_self,mem_write,
      BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64),BitVec.setWidth_eq]
  · intro q hq
    exact gpr_write_of_ne _ _ _ hq

theorem frame_write_word (m : Mem) (p : Addr) (v : BitVec 32) :
    Frame [⟨p,4⟩] m (m.writeW p v) := by
  intro x hx
  simp only [Mem.writeW,Mem.write]
  exact ite_eq_right (fun h => hx _ List.mem_cons_self h)

theorem stores_run (s : State) (n : Nat) (hn : n ≤ 4)
    (hwrite : ∀ i < 4, InRegions s.wr (s.gpr .x5 + BitVec.ofNat 64 (768+4*i)) 4) :
    ∃ t, runBlock isa ((List.range n).flatMap fun i =>
        [.rev32 (wordReg (3-i)) (wordReg (3-i)),.str .w (wordReg (3-i)) .x5 (768+4*i)]) s = some t ∧
      (∀ j < n, t.mem.readW (s.gpr .x5 + BitVec.ofNat 64 (768+4*j)) 32 = rev32 (words s (3-j))) ∧
      (∀ r, (∀ j < n, r ≠ wordReg (3-j)) → t.gpr r = s.gpr r) ∧
      Frame [⟨s.gpr .x5+BitVec.ofNat 64 768,16⟩] s.mem t.mem ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.v = s.v := by
  induction n with
  | zero => exact ⟨s,rfl,fun _ h => absurd h (by omega_using []),fun _ _ => rfl,Frame.refl _ _,rfl,rfl,rfl,rfl⟩
  | succ n ih =>
    obtain ⟨a,ae,aw,ag,af,ard,awr,asp,avec⟩ := ih (by omega_using [hn])
    have ab : a.gpr .x5 = s.gpr .x5 := ag _ (fun j hj => (wordReg_ne_base (3-j) (by omega_using [])).symm)
    have av : a.gpr (wordReg (3-n)) = s.gpr (wordReg (3-n)) := ag _ (fun j hj he => by
      have := wordReg_inj (3-n) (by omega_using []) (3-j) (by omega_using []) he
      omega_using [hn, hj, this])
    have ar : InRegions a.wr (a.gpr .x5 + BitVec.ofNat 64 (768+4*n)) 4 := by
      rw [awr,ab]
      exact hwrite n (by omega_using [hn])
    obtain ⟨b,be,bm,bg,brd,bwr,bsp,bvec⟩ := storeWord_run (wordReg_ne_base (3-n) (by omega_using [])) (by omega_using [hn]) ar
    have bmem : b.mem = a.mem.writeW (s.gpr .x5 + BitVec.ofNat 64 (768+4*n)) (rev32 (words s (3-n))) := by
      simpa only [ab,av,words] using bm
    have bf : Frame [⟨s.gpr .x5 + BitVec.ofNat 64 (768+4*n),4⟩] a.mem b.mem := by
      rw [bmem]
      exact frame_write_word _ _ _
    refine ⟨b,?_,?_,?_,?_,brd.trans ard,bwr.trans awr,bsp.trans asp,bvec.trans avec⟩
    · rw [List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,
        VG.Interleave.runBlock_append,ae,Option.bind_some,be]
    · intro j hj
      by_cases h : j = n
      · subst j
        rw [bmem,Mem.readW_writeW_self32]
      · rw [bf.readW (w := 32) (Region.contains_self _ _) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst r
          exact VG.Offset.disjoint (s.gpr .x5) (by omega_using [h]) (by omega_using [hn, hj]) (by omega_using [hn])) (by decide)]
        exact aw j (by omega_using [hj, h])
    · intro r hr
      exact (bg r (hr n (by omega_using []))).trans (ag r (fun j hj => hr j (by omega_using [hj])))
    · refine af.trans (bf.sub (fun r hr => ?_))
      simp only [List.mem_singleton] at hr; subst r
      refine ⟨_,List.mem_cons_self,?_⟩
      rw [← VG.Offset.add_add (s.gpr .x5) 768 (4*n)]
      exact VG.Offset.sub_base _ (by omega_using [hn] : 4*n+4 ≤ 16)

theorem stored_bytes {m : Mem} {p : Addr} {z : Nat → BitVec 32}
    (h : ∀ i < 4, m.readW (p + BitVec.ofNat 64 (4*i)) 32 = rev32 (z (3-i))) :
    Spec.Aes.bytesAt m p 16 = (VG.Proof.Sm4.outBlock z).toList := by
  apply List.ext_getElem (by simp [Spec.Aes.bytesAt])
  intro i hi hi'
  have hi16 : i < 16 := by simpa [Spec.Aes.bytesAt] using hi
  simp only [Spec.Aes.bytesAt,List.getElem_map,List.getElem_range,Vector.getElem_toList]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have b := Mem.readW_byte m (p+BitVec.ofNat 64 (4*(i/4))) (i := i%4) (by omega_using [])
  rw [VG.Offset.add_add,show 4*(i/4)+i%4 = i by omega_using [],h (i/4) (by omega_using [hi16])] at b
  rw [b,BitVec.getLsbD_extractLsb',VG.Proof.Sm4.getLsbD_outBlock' z hi16 hj]
  simp only [hj,decide_true,Bool.true_and]
  change (byteRev32 (z (3-i/4))).getLsbD (8*(i%4)+j) = _
  rw [byteRev32_getLsbD _ (by omega_using [hj])]
  congr 1 <;> omega_using [hj]

end VG.Proof.Sm4.AArch64.Serial

end

end

/-! ### `Sm4.AArch64.Serial.Rounds`, which only this module used -/

section

/-! # The 32 serial SM4 rounds -/

@[expose] public section

namespace VG.Proof.Sm4.AArch64.Serial

open VG VG.AArch64 VG.Impl.Sm4.AArch64.Serial
open VG.Proof.Sm4 (sround quad quads)

def written : List Reg := [.x6,.x7,.x8,.x9,.x10,.x11]

def steps (K : Nat → BitVec 32) (n : Nat) (x : Nat → BitVec 32) : Nat → BitVec 32 :=
  (List.range n).foldl (fun z i => sround .enc (K i) (i%4) z) x

theorem steps_succ (K : Nat → BitVec 32) (n : Nat) (x : Nat → BitVec 32) :
    steps K (n+1) x = sround .enc (K n) (n%4) (steps K n x) := by
  simp only [steps,List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil]

theorem sround_congr (k : BitVec 32) {a w : Nat} {x y : Nat → BitVec 32}
    (ha : a < 4) (h : ∀ j < 4, x j = y j) (hw : w < 4) :
    sround .enc k a x w = sround .enc k a y w := by
  unfold sround
  split
  · rw [h a ha,h _ (Nat.mod_lt _ (by decide)),h _ (Nat.mod_lt _ (by decide)),
      h _ (Nat.mod_lt _ (by decide))]
  · exact h w hw

theorem steps_congr (K L : Nat → BitVec 32) (n : Nat) (x y : Nat → BitVec 32)
    (hk : ∀ i < n, K i = L i) (hx : ∀ j < 4, x j = y j) :
    ∀ w < 4, steps K n x w = steps L n y w := by
  induction n with
  | zero => exact hx
  | succ n ih =>
    intro w hw
    rw [steps_succ,steps_succ,hk n (by omega_using [])]
    exact sround_congr _ (Nat.mod_lt _ (by decide)) (ih (fun i hi => hk i (by omega_using [hi]))) hw

theorem wordReg_mem : ∀ j < 4, wordReg j ∈ written := by decide

theorem rounds_run (s : State) (n : Nat) (hn : n ≤ 32)
    (hc : Constants s) (ht : Table s)
    (hr : ∀ i < 32, InRegions (s.rd ++ s.wr) (s.gpr .x5 + BitVec.ofNat 64 (256+4*i)) 4) :
    ∃ t, runBlock isa ((List.range n).flatMap round) s = some t ∧
      (∀ w < 4, words t w = steps
        (fun i => s.mem.readW (s.gpr .x5 + BitVec.ofNat 64 (256+4*i)) 32) n (words s) w) ∧
      Constants t ∧ Table t ∧
      (∀ r, r ∉ written → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  induction n with
  | zero => exact ⟨s,rfl,fun _ _ => rfl,hc,ht,fun _ _ => rfl,rfl,rfl,rfl,rfl⟩
  | succ n ih =>
    obtain ⟨a,ae,aw,ac,atab,ag,am,ard,awr,asp⟩ := ih (by omega_using [hn])
    have ab : a.gpr .x5 = s.gpr .x5 := ag _ (by decide)
    have ar : InRegions (a.rd ++ a.wr) (a.gpr .x5 + BitVec.ofNat 64 (256+4*n)) 4 := by
      rw [ard,awr,ab]
      exact hr n (by omega_using [hn])
    obtain ⟨b,be,bw,bc,bt,bg,bm,brd,bwr,bsp⟩ := round_run (by omega_using [hn]) ac atab ar
    refine ⟨b,?_,?_,bc,bt,?_,bm.trans am,brd.trans ard,bwr.trans awr,bsp.trans asp⟩
    · rw [List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,
        VG.Interleave.runBlock_append,ae,Option.bind_some,be]
    · intro w hw
      rw [bw w hw,am,ab,steps_succ]
      exact sround_congr _ (Nat.mod_lt _ (by decide)) aw hw
    · intro r hr
      have hreg : r ≠ wordReg (n%4) := fun he => hr (he ▸ wordReg_mem _ (Nat.mod_lt _ (by decide)))
      have h10 : r ≠ .x10 := fun he => hr (by simp [written,he])
      have h11 : r ≠ .x11 := fun he => hr (by simp [written,he])
      exact (bg r hreg h10 h11).trans (ag r hr)

theorem steps_quads (K : Nat → BitVec 32) (x : Nat → BitVec 32) (n : Nat) :
    steps K (4*n) x = quads .enc K n x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [steps,VG.Proof.Sm4.range_four,List.foldl_append,List.foldl_cons,List.foldl_nil]
    change sround .enc (K (4*n+3)) ((4*n+3)%4)
      (sround .enc (K (4*n+2)) ((4*n+2)%4)
        (sround .enc (K (4*n+1)) ((4*n+1)%4)
          (sround .enc (K (4*n)) ((4*n)%4) (steps K (4*n) x)))) = _
    rw [ih,show (4*n)%4 = 0 by omega_using [],show (4*n+1)%4 = 1 by omega_using [],
      show (4*n+2)%4 = 2 by omega_using [],show (4*n+3)%4 = 3 by omega_using []]
    rfl

end VG.Proof.Sm4.AArch64.Serial

end

end


/-! # Correctness of the single-block SM4 core -/

@[expose] public section

namespace VG.Proof.Sm4.AArch64.Serial

open VG VG.AArch64 VG.Impl.Sm4.AArch64.Serial
open VG.Proof.Modes.AArch64 (ScrIn coreRegion bufRegion)

theorem crypt_wp {s : State} {B : Addr} {k : Spec.Sm4.Schedule}
    (hB : s.gpr .x5 = B) (hs : ScrIn s B core.total) (ready : Ready s.mem B k) :
    WP isa core.crypt s fun t => t.gpr .x5 = B ∧
      t.gpr .x23 = s.gpr .x23 ∧ t.gpr .x24 = s.gpr .x24 ∧ Ready t.mem B k ∧
      Frame [coreRegion core B] s.mem t.mem ∧
      Spec.Aes.bytesAt t.mem (B+BitVec.ofNat 64 768) 16 =
        Spec.Sm4.cipher k (Spec.Aes.bytesAt s.mem (B+BitVec.ofNat 64 768) 16) ∧
      t.rd = s.rd ∧ t.wr = s.wr := by
  have readable : InRegions (s.rd ++ s.wr) (s.gpr .x5) 256 := by
    rw [hB]
    exact ⟨_,List.mem_append_right _ hs.wr,by
      change (⟨B,3264⟩ : Region).Contains B 256
      simp [Region.Contains]⟩
  have bytes : ∀ j < 256, s.mem (s.gpr .x5+BitVec.ofNat 64 j) = Spec.Sm4.sbox.getD j 0 := by
    rw [hB]; exact ready.sbox
  change WP isa (.block (loadSbox ++ quarterConstants ++ loadBlock ++ (List.range 32).flatMap round ++ storeBlock)) s _
  rw [WP.block_append_iff,WP.block_append_iff,WP.block_append_iff,WP.block_append_iff]
  refine WP.mono (loadSbox_ok s readable bytes) fun a ⟨atab,ae⟩ => ?_
  obtain ⟨b,be,bc,bg,bm,brd,bwr,_,bvec⟩ := quarterConstants_run a
  refine WP.of_runBlock ⟨b,be,?_⟩
  have ab : a.gpr = s.gpr := by rw [ae]
  have am : a.mem = s.mem := by rw [ae]
  have ard : a.rd = s.rd := by rw [ae]
  have awr : a.wr = s.wr := by rw [ae]
  have bbase : b.gpr .x5 = B := (bg _ (by decide)).trans (by rw [ab]; exact hB)
  have bmem : b.mem = s.mem := bm.trans am
  have btab : Table b := atab.of_rows (fun j hj => by
    have hn := VG.AArch64.Tbl.treg_ne8 j hj
    exact bvec _ hn.2.2.2.2.1 hn.2.2.2.2.2.1 hn.2.2.2.2.2.2.1)
  have br : ∀ i < 4, InRegions (b.rd ++ b.wr) (b.gpr .x5+BitVec.ofNat 64 (768+4*i)) 4 := by
    intro i hi
    rw [brd,bwr,ard,awr,bbase]
    exact ⟨_,List.mem_append_right _ hs.wr,VG.Offset.contains_base B
      (by omega_using [hi] : 768+4*i+4 ≤ 3264) (by omega_using [hi])⟩
  obtain ⟨c,ce,cw,cg,cm,crd,cwr,_,cvec⟩ := loads_run b 4 (by decide) br
  refine WP.of_runBlock ⟨c,ce,?_⟩
  have ck : ∀ r, r ∉ written → c.gpr r = b.gpr r := by
    intro r hr
    exact cg r (fun j hj he => hr (he ▸ wordReg_mem j hj))
  have cbase : c.gpr .x5 = B := (ck _ (by decide)).trans bbase
  have cmem : c.mem = s.mem := cm.trans bmem
  have cc : Constants c := by simpa only [Constants,cvec] using bc
  have ct : Table c := by simpa only [Table,cvec] using btab
  have cr : ∀ i < 32, InRegions (c.rd ++ c.wr) (c.gpr .x5+BitVec.ofNat 64 (256+4*i)) 4 := by
    intro i hi
    rw [crd,cwr,brd,bwr,ard,awr,cbase]
    exact ⟨_,List.mem_append_right _ hs.wr,VG.Offset.contains_base B
      (by omega_using [hi] : 256+4*i+4 ≤ 3264) (by omega_using [hi])⟩
  obtain ⟨d,de,dw,dc,dt,dg,dm,drd,dwr,_⟩ :=
    rounds_run c 32 (by decide) cc ct cr
  refine WP.of_runBlock ⟨d,de,?_⟩
  have dbase : d.gpr .x5 = B := (dg _ (by decide)).trans cbase
  have dmem : d.mem = s.mem := dm.trans cmem
  let init := VG.Proof.Sm4.ofBlock (Spec.Sm4.blockAt s.mem (B+BitVec.ofNat 64 768))
  let z := VG.Proof.Sm4.quads .enc (fun i => k.getD i 0) 8 init
  have initial : ∀ w < 4, words c w = init w := by
    intro w hw
    rw [cw w hw,bmem,bbase,← VG.Offset.add_add B 768 (4*w),readBE_word _ _ w hw]
    rfl
  have dwords : ∀ w < 4, words d w = z w := by
    intro w hw
    rw [dw w hw]
    have h := steps_congr
      (fun i => c.mem.readW (c.gpr .x5+BitVec.ofNat 64 (256+4*i)) 32)
      (fun i => k.getD i 0) 32 (words c) init
      (fun i hi => by rw [cmem,cbase]; exact ready.keys i hi) initial w hw
    rw [h]
    change steps (fun i => k.getD i 0) (4*8) init w = z w
    rw [steps_quads]
  have dr : ∀ i < 4, InRegions d.wr (d.gpr .x5+BitVec.ofNat 64 (768+4*i)) 4 := by
    intro i hi
    rw [dwr,cwr,bwr,awr,dbase]
    exact ⟨_,hs.wr,VG.Offset.contains_base B (by omega_using [hi] : 768+4*i+4 ≤ 3264) (by omega_using [hi])⟩
  obtain ⟨e,ee,ew,eg,ef,erd,ewr,_,_⟩ := stores_run d 4 (by decide) dr
  refine WP.of_runBlock ⟨e,ee,?_⟩
  have ek : ∀ r, r ∉ written → e.gpr r = d.gpr r := by
    intro r hr
    exact eg r (fun j hj he => hr (he ▸ wordReg_mem (3-j) (by omega_using [])))
  have output : Spec.Aes.bytesAt e.mem (B+BitVec.ofNat 64 768) 16 = (VG.Proof.Sm4.outBlock z).toList := by
    apply stored_bytes
    intro i hi
    rw [VG.Offset.add_add]
    rw [← dbase,ew i hi,dwords (3-i) (by omega_using [])]
  have frame : Frame [bufRegion core B] s.mem e.mem := by
    change Frame [⟨B+BitVec.ofNat 64 768,16⟩] s.mem e.mem
    simpa only [dbase,dmem] using ef
  have finalReady : Ready e.mem B k := ready.frame frame (fun r hr => by
    simp only [List.mem_singleton] at hr; subst r
    exact Or.inr (fun _ h => h))
  refine ⟨(ek _ (by decide)).trans dbase,?_,?_,finalReady,?_,?_,?_,?_⟩
  · rw [ek _ (by decide),dg _ (by decide),ck _ (by decide),bg _ (by decide),ab]
  · rw [ek _ (by decide),dg _ (by decide),ck _ (by decide),bg _ (by decide),ab]
  · exact frame.sub (fun r hr => by
      simp only [List.mem_singleton] at hr; subst r
      exact ⟨_,List.mem_cons_self,VG.Offset.sub_base B (by decide : 768+16 ≤ 3168)⟩)
  · rw [output,VG.Proof.Sm4.cipher_bytes]
  · exact erd.trans (drd.trans (crd.trans (brd.trans ard)))
  · exact ewr.trans (dwr.trans (cwr.trans (bwr.trans awr)))

end VG.Proof.Sm4.AArch64.Serial

end

end


/-! # The single-block SM4 core meets the existing mode interface -/

@[expose] public section

namespace VG.Proof.Sm4.AArch64.Serial

open VG VG.AArch64 VG.Impl.Sm4.AArch64.Serial
open VG.Proof.Modes.AArch64 (CoreSpec BlockSpec KeepsReg bufAddr)

@[simp] theorem core_bw : core.bw = 2 := rfl

def coreSpec : CoreSpec core where
  Key := Spec.Sm4.Schedule
  cipher := Spec.Sm4.cipher
  KeyArgs := VG.Proof.Sm4.AArch64.KeyArgs
  Ready s B k := Ready s.mem B k
  cipher_len _ _ := by simp [Spec.Sm4.cipher]
  layout := ⟨by decide,by decide,by decide,by decide,by decide⟩
  keyRegs_ok := by decide
  regs_ok := by decide
  keyArgs_congr h hr hrd hwr _ hf := VG.Proof.Sm4.AArch64.keyArgs_congr h hr hrd hwr hf
  ready_frame h hf hd _ _ := h.frame hf hd
  prepare_wp := prepare_wp
  crypt_wp := by
    intro s B k hb hs hr
    refine WP.mono (crypt_wp hb hs hr) fun t ⟨tb,td,tl,tr,tf,to,rd,wr⟩ =>
      ⟨tb,td,tl,tr,tf,?_,rd,wr⟩
    intro j hj
    have hj' : j < 1 := hj
    have hj0 : j = 0 := by omega_using [hj']
    subst j
    change Spec.Aes.bytesAt t.mem (B+BitVec.ofNat 64 (768+16*0)) 16 =
      Spec.Sm4.cipher k (Spec.Aes.bytesAt s.mem (B+BitVec.ofNat 64 (768+16*0)) 16)
    exact to

abbrev blockSpec : BlockSpec core := coreSpec.toBlock rfl

theorem prepare_regSafe_x19 : VG.Proof.Modes.AArch64.regSafe .x19 core.prepare = true := by
  show VG.Proof.Modes.AArch64.regSafe .x19 (.seq (.block preparedTable) copySchedule) = true
  rw [VG.Proof.Sm4.AArch64.serialTable.lit_eq]
  decide +kernel

theorem crypt_regSafe_x19 : VG.Proof.Modes.AArch64.regSafe .x19 core.crypt = true := by decide +kernel

theorem keeps_x19 : KeepsReg .x19 core.prepare ∧ KeepsReg .x19 core.crypt :=
  ⟨VG.Proof.Modes.AArch64.keepsReg_of_regSafe prepare_regSafe_x19,
    VG.Proof.Modes.AArch64.keepsReg_of_regSafe crypt_regSafe_x19⟩

attribute [local irreducible] Spec.Sm4.cipher in
theorem cipher_eq (k : Spec.Sm4.Schedule) : blockSpec.cipher k = Spec.Sm4.cipher k := rfl

end VG.Proof.Sm4.AArch64.Serial
