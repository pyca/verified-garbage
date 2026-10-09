import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedFinalCheck
import VerifiedGarbage.Proof.MlDsa.Round.Ones

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.Spec.MlDsa

def sumN (n : Nat) (f : Nat → Nat) : Nat := ((List.range n).map f).sum

theorem sumN_succ (n : Nat) (f : Nat → Nat) : sumN (n+1) f=sumN n f+f n := by
  simp [sumN,List.range_succ]

theorem sumN_add (n : Nat) (f g : Nat → Nat) :
    sumN n (fun i => f i+g i)=sumN n f+sumN n g := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [sumN_succ,ih]; omega

theorem sumN_swap (m n : Nat) (f : Nat → Nat → Nat) :
    sumN m (fun i => sumN n (f i))=sumN n (fun j => sumN m (fun i => f i j)) := by
  induction m with
  | zero => simp [sumN]
  | succ m ih => simp only [sumN_succ,ih,sumN_add]

theorem sumN_append (m n : Nat) (f : Nat → Nat) :
    sumN (m+n) f=sumN m f+sumN n (fun i => f (m+i)) := by
  induction n with
  | zero => simp [sumN]
  | succ n ih => rw [show m+(n+1)=(m+n)+1 by omega,sumN_succ,ih,sumN_succ]; omega

theorem sumN_blocks (m n : Nat) (f : Nat → Nat) :
    sumN m (fun i => sumN n (fun j => f (n*i+j)))=sumN (n*m) f := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [sumN_succ,ih,Nat.mul_succ,sumN_append]

theorem pairedHintSum_order (f : Nat → Nat → Nat) :
    sumN 4 (fun e => sumN 8 (fun u => sumN 2 (fun p => sumN 8 (fun j => f p (4*u+32*j+e)))))=
      sumN 2 (fun p => sumN 256 (f p)) := by
  rw [sumN_swap 4 8]
  conv_lhs => arg 2; ext u; rw [sumN_swap 4 2]
  rw [sumN_swap 8 2]
  apply congrArg (sumN 2)
  funext p
  conv_lhs => arg 2; ext u; rw [sumN_swap 4 8]
  rw [sumN_swap 8 8]
  have he : (fun j => sumN 8 (fun u => sumN 4 (fun e => f p (4*u+32*j+e))))=
      (fun j => sumN 32 (fun k => f p (32*j+k))) := by
    funext j
    rw [←sumN_blocks 8 4 (fun k => f p (32*j+k))]
    congr 1
    funext u
    congr 1
    funext e
    congr 1
    omega
  rw [he,sumN_blocks 8 32]

theorem sumN_four (f : Nat → Nat) : sumN 4 f=f 0+f 1+f 2+f 3 := by
  change f 0+(f 1+(f 2+(f 3+0)))=f 0+f 1+f 2+f 3
  omega

theorem map_finRange_nat (n : Nat) (f : Nat → Nat) :
    (List.finRange n).map (fun i => f i.val)=(List.range n).map f := by
  apply List.ext_getElem
  · simp
  · intro i hi hi
    simp

theorem allChecks_sum (f : Nat → Nat → Nat) :
    (allChecks.map fun i => f i.1.val i.2.val).sum=sumN 2 (fun p => sumN 8 (f p)) := by
  simp only [allChecks,List.map_flatMap,List.map_map]
  simp only [List.flatMap, List.sum_flatten,List.map_map]
  simp only [Function.comp_def,map_finRange_nat,sumN]
  rw [map_finRange_nat 2 (fun p => ((List.range 8).map (f p)).sum)]

theorem onesTo_sum (h : Vector Bool n) (i : Nat) :
    VG.Proof.MlDsa.Round.onesTo h i=sumN i (fun j => h[j]!.toNat) := by
  induction i with
  | zero => rfl
  | succ i ih => rw [VG.Proof.MlDsa.Round.onesTo_succ,ih,sumN_succ]

theorem hintOnes_pair_sum (f : Nat → Vector Bool n) :
    hintOnes ((List.range 2).map f)=sumN 2 (fun p => sumN 256 (fun k => (f p)[k]!.toNat)) := by
  unfold hintOnes sumN
  rw [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p _
  have h := VG.Proof.MlDsa.Round.hintOnes_onesTo (f p)
  rw [onesTo_sum] at h
  simpa only [Function.comp_def,hintOnes,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero,n,sumN] using h

end VG.Proof.MlDsa.AArch64.Optimized.Paired
