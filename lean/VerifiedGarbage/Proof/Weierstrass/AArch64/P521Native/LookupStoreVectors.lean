module

-- separate module: this consolidated proof replays 0.47s of elaboration/kernel work versus 0.28s importing its dependencies (local Lean trace); retaining the boundary avoids replaying it in its sole importer.

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.LookupEntry
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Mont.AArch64.Words
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem64

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64

theorem readVectors_length (m : Mem) (p : Addr) (d n : Nat) : (readVectors m p d n).length=n := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih => simp only [readVectors,List.length_cons,ih]

theorem readVectors_getD (m : Mem) (p : Addr) : ∀{n j d : Nat},j<n →
    (readVectors m p d n).getD j 0=m.read (p+BitVec.ofNat 64 (d+16*j)) 16
  | 0,_,_,h => False.elim (Nat.not_lt_zero _ h)
  | n+1,0,d,_ => by simp only [readVectors,List.getD_cons_zero,Nat.mul_zero,Nat.add_zero]
  | n+1,j+1,d,h => by
    rw [readVectors,List.getD_cons_succ,readVectors_getD m p (by omega_arith)]
    rw [show d+16*(j+1)=(d+16)+16*j by omega_arith]

theorem lookup_entry_vector {s : State} {table : Addr} {d : Nat} (k : Nat)
    (hk : 1≤k ∧ k≤16) (hd : d≤16) (digit : s.gpr .x2=BitVec.ofNat 64 d) (zero : s.gpr .x3=0)
    (ht : LookupTableReadable s table) :
    WP isa (.block (lookupEntryCode k)) s fun t =>
      (∀j (hj : j<9),t.v (lookupAccs[j])=s.v (lookupAccs[j]) |||
        (if d=k then s.mem.read (table+BitVec.ofNat 64 (lookupEntryOffset k+16*j)) 16 else 0)) ∧
      VKeep [.x4,.x16,.x17] (.v17::.v18::lookupAccs) s t := by
  refine WP.mono (lookup_entry_ok k hk hd digit zero ht) fun t ⟨values,frame⟩ => ⟨?_,frame⟩
  intro j hj
  have hl : j<lookupAccs.length := hj
  have hr : j<(readVectors s.mem (table+BitVec.ofNat 64 (lookupEntryOffset k)) 0 9).length := by rw [readVectors_length]; exact hj
  have h := congrArg (fun xs : List (BitVec 128) => xs.getD j 0) values
  have hL : j<(lookupAccs.map t.v).length := by simpa only [List.length_map] using hl
  have hR : j<(List.zipWith (fun x y => x ||| if d=k then y else 0) (lookupAccs.map s.v)
      (readVectors s.mem (table+BitVec.ofNat 64 (lookupEntryOffset k)) 0 9)).length := by
    simp only [List.length_zipWith,List.length_map,readVectors_length,show lookupAccs.length=9 from rfl,Nat.min_self]
    exact hj
  rw [←List.getElem_eq_getD (h:=hL) 0,←List.getElem_eq_getD (h:=hR) 0] at h
  simp only [List.getElem_map,List.getElem_zipWith] at h
  have read := readVectors_getD s.mem (table+BitVec.ofNat 64 (lookupEntryOffset k)) (n:=9) (j:=j) (d:=0) hj
  rw [←List.getElem_eq_getD (h:=hr) 0] at read
  simp only [Nat.zero_add,VG.Offset.add_ofNat_add_ofNat] at read
  rw [read] at h
  exact h

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Weierstrass.AArch64

def lookupScanCode (k : Nat) : Nat → List Instr
  | 0 => []
  | n+1 => lookupEntryCode k++lookupScanCode (k+1) n

def tableColumn (m : Mem) (table : Addr) (j k : Nat) : Nat → List (BitVec 128)
  | 0 => []
  | n+1 => m.read (table+BitVec.ofNat 64 (lookupEntryOffset k+16*j)) 16::tableColumn m table j (k+1) n

theorem tableColumn_length (m : Mem) (table : Addr) (j k n : Nat) : (tableColumn m table j k n).length=n := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih => simp only [tableColumn,List.length_cons,ih]

theorem tableColumn_getD (m : Mem) (table : Addr) (j : Nat) : ∀{n i k : Nat},i<n →
    (tableColumn m table j k n).getD i 0=m.read (table+BitVec.ofNat 64 (lookupEntryOffset (k+i)+16*j)) 16
  | 0,_,_,h => False.elim (Nat.not_lt_zero _ h)
  | n+1,0,k,_ => by simp only [tableColumn,List.getD_cons_zero,Nat.add_zero]
  | n+1,i+1,k,h => by
    rw [tableColumn,List.getD_cons_succ,tableColumn_getD m table j (by omega_arith)]
    rw [show k+(i+1)=(k+1)+i by omega_arith]

theorem lookupScan_source : lookupScanCode 1 16=lookupEntriesCode := by lit_decide

theorem lookup_scan_ok {d : Nat} (hd : d≤16) : ∀(n k : Nat) {s : State} {table : Addr},
    1≤k → k+n≤17 → s.gpr .x2=BitVec.ofNat 64 d → s.gpr .x3=0 → LookupTableReadable s table →
    WP isa (.block (lookupScanCode k n)) s fun t =>
      (∀j(hj : j<9),t.v lookupAccs[j]=scanWords (tableColumn s.mem table j k n) k d (s.v lookupAccs[j])) ∧
      VKeep [.x4,.x16,.x17] (.v17::.v18::lookupAccs) s t
  | 0,k,s,table,_,_,_,_,_ => WP.block_nil ⟨fun _ _ => rfl,VKeep.refl _ _ s⟩
  | n+1,k,s,table,hk,hn,digit,zero,readable => by
    rw [lookupScanCode,WP.block_append_iff]
    refine WP.mono (lookup_entry_vector k ⟨hk,by omega_arith⟩ hd digit zero readable)
      fun u ⟨entry,ku⟩ => ?_
    have ht : LookupTableReadable u table :=
      ⟨(ku.gpr .x26 (by decide)).trans readable.reg,by intro i hi; rw [ku.rd,ku.wr]; exact readable.read i hi⟩
    refine WP.mono (lookup_scan_ok hd n (k+1) (by omega_arith) (by omega_arith)
      ((ku.gpr .x2 (by decide)).trans digit) ((ku.gpr .x3 (by decide)).trans zero) ht)
      fun t ⟨rest,kt⟩ => ?_
    refine ⟨?_,ku.trans kt⟩
    intro j hj
    have e := rest j hj
    rw [ku.mem,entry j hj] at e
    exact e

theorem lookup_scan_sixteen {s : State} {table : Addr} {d : Nat} (hd : d≤16)
    (digit : s.gpr .x2=BitVec.ofNat 64 d) (zero : s.gpr .x3=0) (readable : LookupTableReadable s table)
    (identity : Nat → BitVec 128)
    (initial : ∀j(hj : j<9),s.v lookupAccs[j]=(if d=0 then identity j else 0)) :
    WP isa (.block lookupEntriesCode) s fun t =>
      (∀j(hj : j<9),t.v lookupAccs[j]=(if d=0 then identity j else
        s.mem.read (table+BitVec.ofNat 64 (lookupEntryOffset d+16*j)) 16)) ∧
      VKeep [.x4,.x16,.x17] (.v17::.v18::lookupAccs) s t := by
  rw [←lookupScan_source]
  refine WP.mono (lookup_scan_ok hd 16 1 (by decide) (by decide) digit zero readable) fun t ⟨out,k⟩ => ⟨?_,k⟩
  intro j hj
  have e := out j hj
  rw [initial j hj,scan_sixteen _ (tableColumn_length _ _ _ _ _) d hd (identity j)] at e
  by_cases h : d=0
  · simpa only [h,ite_true] using e
  · simp only [h,ite_false] at e ⊢
    rw [tableColumn_getD s.mem table j (by omega_arith : d-1<16)] at e
    rw [show 1+(d-1)=d by omega_arith] at e
    exact e

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Weierstrass.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64

def lookupVectorStores (f : Nat → VReg) (k : Nat) : List Instr :=
  (List.range k).map (fun i => Instr.strq (f i) .x17 (16*i))

theorem lookup_vector_stores_ok {size : Nat} (f : Nat → VReg) {s : State} {base : Addr}
    (hs : Scr s base size) (ptr : s.gpr .x17=off base 1504) : ∀k,1504+16*k≤size →
    WP isa (.block (lookupVectorStores f k)) s fun t =>
      (∀j<2*k,word t.mem base (1504+8*j)=vdword (s.v (f (j/2))) (j%2)) ∧
      KeepRegs [] s t ∧ t.v=s.v ∧ Outside base 1504 (16*k) s.mem t.mem
  | 0,_ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _),⟨fun _ _ => rfl,rfl,rfl,rfl⟩,rfl,Outside.refl _ _ _ _⟩
  | k+1,hk => by
    have hn := hs.nowrap
    have he := hs.enc
    simp only [lookupVectorStores,List.range_succ,List.map_append,List.map_cons,List.map_nil]
    rw [WP.block_append_iff]
    refine WP.mono (lookup_vector_stores_ok f hs ptr k (by omega_arith)) fun u ⟨words,ku,vu,ou⟩ => ?_
    have up : u.gpr .x17=off base 1504 := (ku.gpr .x17 (by simp)).trans ptr
    have hsu : Scr u base size := hs.of_keepRegs ku (by simp)
    refine wp_strq (by constructor <;> omega_arith)
      (by rw [up,ku.wr,VG.Offset.add_ofNat_add_ofNat]; exact ⟨_,hs.wr,hs.contains (by omega_arith) (by decide)⟩) ?_
    rw [up,vu,←ofVDwords_vdword (s.v (f k)),write16_dwords,VG.Offset.add_ofNat_add_ofNat,
      VG.Offset.add_ofNat_add_ofNat]
    have oa := writeW_outside u.mem base (d:=1504+16*k) (vdword (s.v (f k)) 0) (by omega_arith)
    have ob := writeW_outside (u.mem.writeW (off base (1504+16*k)) (vdword (s.v (f k)) 0)) base
      (d:=1504+16*k+8) (vdword (s.v (f k)) 1) (by omega_arith)
    refine ⟨?_,ku.trans ⟨fun _ _ => rfl,rfl,rfl,rfl⟩,rfl,?_⟩
    · intro j hj
      rcases Nat.lt_or_ge j (2*k) with low|high
      · rw [ob.word (by omega_arith) (by omega_arith),oa.word (by omega_arith) (by omega_arith),words j low]
      · rcases Nat.lt_or_ge j (2*k+1) with lo|hi
        · have eq : j=2*k := by omega_arith
          subst j
          rw [ob.word (by omega_arith) (by omega_arith),show 1504+8*(2*k)=1504+16*k by omega_arith,
            word_writeW_self,show 2*k/2=k by omega_arith,show 2*k%2=0 by omega_arith]
        · have eq : j=2*k+1 := by omega_arith
          subst j
          rw [show 1504+8*(2*k+1)=1504+16*k+8 by omega_arith,word_writeW_self,
            show (2*k+1)/2=k by omega_arith,show (2*k+1)%2=1 by omega_arith]
    · exact (ou.mono (by decide) (by omega_arith)).trans
        ((oa.mono (by omega_arith) (by omega_arith)).trans (ob.mono (by omega_arith) (by omega_arith)))

end VG.Proof.Weierstrass.AArch64.P521Native
