module
public import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.PackedNaf
public import VerifiedGarbage.Proof.Ecdh.AArch64.Window
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.P256Bounds
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.State
import VerifiedGarbage.Proof.Ecdsa.AArch64.SlotOps
@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.P521
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64
open VG.Impl.Ecdh.AArch64 (PX PY)
abbrev packedQ (c : Cfg) := Impl.Ecdsa.Verify.AArch64.Cfg.packedNafQ c
def packedTblI : List Nat := (List.range 24).map (71 + ·)
variable {c : Cfg}
theorem packedTbl_eq (c : Cfg) : winTblSlots (packedQ c) = packedTblI.map c.sl := by
 simp only [winTblSlots, packedTblI, List.map_map]
 refine List.map_congr_left fun i _ => ?_
 change slot c.n 71 + 8*c.n*i = c.sl (71+i)
 rw [sl_eq c (71+i) (by unfold TMP; omega_arith)]
 simp only [slot, Nat.mul_add, Nat.add_assoc]
theorem packedSlots_eq (c : Cfg) : winSlots (packedQ c) = (roI ++ otherI ++ packedTblI).map c.sl := by
 rw [winSlots,packedTbl_eq,List.map_append,List.map_append]; rfl
theorem packedWs_eq (c : Cfg) : winWs (packedQ c) = (otherI ++ packedTblI).map c.sl := by
 rw [winWs,packedTbl_eq,List.map_append]; rfl
theorem packedW_eq (c : Cfg) : winW (packedQ c) = slW c (otherI ++ packedTblI ++ [TMP]) := by
 rw [winW,packedWs_eq]; simp only [slW,List.map_append,List.map_map]; rfl

theorem packed_lay (hc : CfgOk c) (hn : c.n=9) : Lay (packedQ c).M size (· ∈ winSlots (packedQ c)) := by
 have hl : ∀ i ∈ roI ++ otherI ++ packedTblI, i<112 ∧ i≠MP ∧ i≠TMP ∧ i≠54 := by decide
 rw [packedSlots_eq]
 refine ⟨?_,?_,?_,?_⟩
 · intro x hx; obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
   exact sl_le' c hc.n10 (hl i hi).1
 · intro x y hx hy hxy
   obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
   obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hy
   exact sl_apart c (fun h => hxy (h ▸ rfl)) (.inl (hl i hi).2.2.1) (.inl (hl j hj).2.2.1)
 · intro x hx; obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
   exact sl_apart c (hl i hi).2.1 (.inl (hl i hi).2.2.1) (.inl (by decide))
 · intro x hx; obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
   change c.sl i + 8*c.n ≤ c.sl TMP ∨ c.sl TMP + 8*c.n ≤ c.sl i
   rw [sl_eq c i (hl i hi).2.2.1,sl_tmp c (.inr (.inr hn)),hn]
   have := (hl i hi).2.2.2
   simp only [Mont.moAt]; omega

theorem packedWinLay (hc : CfgOk c) (hn : c.n=9) : WinLay (packedQ c) size := by
 refine ⟨packed_lay hc hn,?_,?_,?_,hc.n0,?_,?_,?_⟩
 · exact (winLayQ hc).ro
 · exact (winLayQ hc).nodup
 · intro x hx
   have hx' : x ∈ (roI ++ otherI).map c.sl := by rw [List.map_append]; exact hx
   obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx'
   have key : ∀ i ∈ roI ++ otherI, i<45 ∧ i≠TMP := by decide
   left
   change c.sl i + 8*c.n ≤ slot c.n 71
   rw [sl_eq c i (key i hi).2,hn]
   have := (key i hi).1
   simp only [slot]; omega
 · exact (winLayQ hc).J
 · exact (winLayQ hc).bits
 · intro w hw
   rw [packedW_eq] at hw
   obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hw
   change c.sl WB + 4*(16*c.n+1) ≤ c.sl i ∨ c.sl i + 8*c.n ≤ c.sl WB
   have key : ∀ i ∈ otherI ++ packedTblI ++ [TMP], i=TMP ∨ (i<WB ∧ i≠TMP) ∨ (71≤i ∧ i≠TMP) := by decide
   rcases key i hi with rfl | ⟨hi,hT⟩ | ⟨hi,hT⟩
   · exact hc.window_tmp
   · exact Or.inr (sl_lt c hi hT)
   · left; rw [sl_eq c WB,sl_eq c i hT,hn]; unfold WB; omega

theorem packedWinA (hc : CfgOk c) : WinA (packedQ c) where
 sl x hx := by
  rw [packedSlots_eq] at hx
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx
  exact sl_mod8 c i
 mod := MP'_A c
 call := (winAQ hc).call
 bits4 := (winAQ hc).bits4

theorem packedCacheAt (c : Cfg) : PubNaf.cacheAt (packedQ c) 1 = 64+8*c.n*95 := by
 change slot c.n 71 + 8*(24*c.n) + 16*c.n*(1-1) = _
 simp only [slot]; omega_arith

theorem packedCacheW (c : Cfg) : PubNaf.cacheW (packedQ c) = [(64+8*c.n*95,128*c.n)] := by
 rw [PubNaf.cacheW,packedCacheAt]; rfl

theorem packed_below (hn : c.n=9) {i : Nat} (hi : i≤94) : c.sl i + 8*c.n ≤ 64+8*c.n*95 := by
 by_cases h : i=TMP
 · subst h; rw [sl_tmp c (.inr (.inr hn)),hn]; decide
 · rw [sl_eq c i h,hn]; omega

theorem packedCacheLay (_hc : CfgOk c) (hn : c.n=9) : PubNaf.CacheLay (packedQ c) size where
 slots := by
  intro x hx; rw [packedSlots_eq] at hx
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
  rw [packedCacheAt]
  exact packed_below hn ((show ∀ i∈roI++otherI++packedTblI,i≤94 by decide) i hi)
 tmp := by rw [packedCacheAt]; exact packed_below hn (i:=TMP) (by decide)
 mo := by rw [packedCacheAt]; exact packed_below hn (i:=MP) (by decide)
 bits := by
  rw [packedCacheAt]
  change c.sl WB + 4*(16*c.n+1) ≤ _
  rw [sl_eq c WB,hn]; decide
 top := by rw [packedCacheAt]; change 64+8*c.n*95+128*c.n≤8192; rw [hn]; decide
 al := by rw [packedCacheAt]; omega

theorem packedNafLay (hc : CfgOk c) (hn : c.n=9) : PubNaf.NafLay (packedQ c) size where
 win := packedWinLay hc hn
 al := packedWinA hc
 n4 := by change c.n≠4; omega
 n6 := by change c.n≤9; omega
 digits := by change 64*c.n+1≤4*(16*c.n+1); omega
 rxy := by change c.sl RY=c.sl RX+8*c.n; simp (disch:=decide) only [sl_eq]; unfold RX RY; omega
 rxz := by change c.sl RZ=c.sl RX+16*c.n; simp (disch:=decide) only [sl_eq]; unfold RX RZ; omega
 exy := by change c.sl TY=c.sl TX+8*c.n; simp (disch:=decide) only [sl_eq]; unfold TX TY; omega
 exz := by change c.sl TZ=c.sl TX+16*c.n; simp (disch:=decide) only [sl_eq]; unfold TX TZ; omega
 cache := packedCacheLay hc hn

theorem fixedOk_packedCache (hn : c.n=9) : FixedOk c (PubNaf.cacheW (packedQ c)) := by
 intro w hw; rw [packedCacheW,List.mem_singleton] at hw; subst hw
 right; have := packed_below hn (i:=12) (by decide); simp only; omega

theorem apart_packedCache (hn : c.n=9) {i : Nat} (hi : i<45) :
 ∀ w∈PubNaf.cacheW (packedQ c),c.sl i+8*c.n≤w.1 ∨ w.1+w.2≤c.sl i := by
 intro w hw; rw [packedCacheW,List.mem_singleton] at hw; subst hw
 exact Or.inl (packed_below hn (by omega))
end VG.Proof.Ecdsa.Verify.AArch64.P521
