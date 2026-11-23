module
public import VerifiedGarbage.Proof.AesGcm.X86_64.Short.BoundedSpans
public import VerifiedGarbage.Proof.AesGcm.X86_64.DirectGather.Post
import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.Mid
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Gcm.Compose
import VerifiedGarbage.Proof.Aes.KeyWords

/-! The two public gather descriptors bind the same source-span contract as the in-place entry. -/
@[expose] public section
namespace VG.Proof.AesGcm.X86_64.DirectGather.Layout
open VG VG.X86_64 Gather Short
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Spec.Aes (bytesAt)
variable {M : CtxMode} {s t : State}

def secondSrc (s : State) : Addr := if Cnt s = 2 then sb s 1 else sb s 0

private theorem one_len (h : Layout M s) (one : Cnt s = 1) : sl s 0 = L s := by
  simpa only [one,gl_succ,gl_zero,Nat.zero_add] using h.glen

private theorem two_len (h : Layout M s) (two : Cnt s = 2) : sl s 0 + sl s 1 = L s := by
  simpa only [two,gl_succ,gl_zero,Nat.zero_add] using h.glen

theorem boundedGeo (h : Layout M s) (cnt : Cnt s = 1 ∨ Cnt s = 2) :
    SpanLayout s (sb s 0) (secondSrc s) (Dst s) (W s) (SP s) (sl s 0) (L s) := by
  have m := slice_mem s (i:=0) (by omega : 0<Cnt s)
  have first : sl s 0 ≤ L s := by
    rcases cnt with c|c
    · exact Nat.le_of_eq (one_len h c)
    · have eq := two_len h c
      omega
  have depth : (below (SP s) 24).Sub (below (SP s) 2512) := below_sub (by decide) (by decide)
  have tail (lt : sl s 0 < L s) : Cnt s = 2 := cnt.resolve_left (fun c => Nat.ne_of_lt lt (one_len h c))
  refine ⟨first,?_,.inr (h.ls _ m).1,(h.ls _ m).2.2,((h.b_ls _ m).sub_left depth).symm,?_,?_,?_,?_⟩
  · rw [h.rd]; exact covers_of_mem (by simp [m])
  all_goals
    intro lt
    have c := tail lt
    have eq : L s - sl s 0 = sl s 1 := by have := two_len h c; omega
    have j := slice_mem s (i:=1) (by omega : 1<Cnt s)
    simp only [secondSrc,c,ite_true,eq]
  · rw [h.rd]; exact covers_of_mem (by simp [j])
  · exact .inr (h.ls _ j).1
  · exact (h.ls _ j).2.2
  · exact ((h.b_ls _ j).sub_left depth).symm

theorem spanPlain (h : Layout M s) (cnt : Cnt s = 1 ∨ Cnt s = 2) :
    spanBytes s (sb s 0) (secondSrc s) (sl s 0) (L s) = pt s (Cnt s) := by
  have base : pt s 0 = [] := rfl
  rcases cnt with c|c
  · have eq := one_len h c
    simp only [spanBytes,←eq,Nat.sub_self,bytesAt,List.range_zero,List.map_nil,List.append_nil,c,pt_succ,base,List.nil_append]
  · have eq : L s-sl s 0=sl s 1 := by have := two_len h c; omega
    simp only [spanBytes,eq,secondSrc,c,ite_true,pt_succ,base,List.nil_append]

theorem boundedDone (h : Layout M s) (cnt : Cnt s = 1 ∨ Cnt s = 2)
    (post : SealPostFrom s (K s) (W s) (SP s) (Dst s) (L s) (R s) (AL s).toNat (hk s)
      (Spec.Gcm.j0 (hk s) (iv s)) (ad s) (spanBytes s (sb s 0) (secondSrc s) (sl s 0) (L s)) t) :
    BodyDone M s t := by
  obtain ⟨env,rd,wr,saved,frame,text,tag⟩ := post
  refine ⟨env,rd,wr,saved,frame.sub ?_,(h.spanPlain cnt) ▸ text,?_⟩
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl
    · exact ⟨_,List.mem_cons_self ..,fun _ x => x⟩
    · exact ⟨dR s,by simp [changed],fun _ x => x⟩
    · exact ⟨below (SP s) 56,by simp [changed],below_sub (by decide) (by decide)⟩
  · rw [Proof.Gcm.fullTag_eq]
    rw [show (ad s).length=(AL s).toNat from VG.Proof.Aes.KeyWords.length_bytesAt .., VG.Proof.Aes.KeyWords.length_bytesAt]
    exact tag

end VG.Proof.AesGcm.X86_64.DirectGather.Layout
