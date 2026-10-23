module

import VerifiedGarbage.Proof.AesCfb.AArch64.Decrypt.Inputs
import VerifiedGarbage.Proof.AesCfb.AArch64.Decrypt.Store
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.AesCfb.AArch64.Decrypt
import VerifiedGarbage.Proof.Aes.AArch64.Aese.Dec
public import VerifiedGarbage.Proof.Aes.AArch64.Ecb
public import VerifiedGarbage.Proof.AesCbc.AArch64.Loop
public import VerifiedGarbage.Proof.Aes.AArch64.Aese.Rounds

/-! # A group of independent decryptions and their sequential CBC stores -/

@[expose] public section

namespace VG.Proof.AesCfb.AArch64.Decrypt

open VG VG.AArch64
open VG.Proof.Aes.AArch64 VG.Proof.Aes.AArch64.Aese
open VG.Impl.Aes.AArch64.Aese
open VG.Proof.AesCbc.AArch64

def chaining (s₀ : State) : Nat → BitVec 128
  | 0 => s₀.mem.readW (Iv s₀) 128
  | k+1 => s₀.mem.readW (blk s₀ k) 128

def output (s₀ : State) (k : Nat) : Spec.Aes.State :=
  Vector.ofFn fun i =>
    (Spec.Aes.cipher (R s₀) (wK s₀) (st (chaining s₀ k))).getD i.1 0 ^^^
      vbyte (s₀.mem.readW (blk s₀ k) 128) i.1

/-- `c` blocks have been stored; the pointer and count are at block `p`. -/
structure Inv (s₀ : State) (c p : Nat) (s : State) : Prop where
  le : c ≤ N s₀
  keys : Keys (R s₀) (wK s₀) s
  x2 : s.gpr .x2 = blk s₀ p
  x3 : s.gpr .x3 = BitVec.ofNat 64 (N s₀-p)
  x11 : s.gpr .x11 = Iv s₀
  chain : s.v .v31 = chaining s₀ c
  data : EcbInv s₀.mem s.mem (Dp s₀) (N s₀) c (output s₀)
  frame : Frame [dataR s₀] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem group_ok {s₀ s : State} (hp : UPre s₀) (b : VReg) (bs : List VReg)
    (hbr : BlockRegs (b::bs)) (h31 : .v31 ∉ b::bs) (hlen : (b::bs).length ≤ 8)
    {c : Nat} (hc : c+(b::bs).length ≤ N s₀)
    (hI : Inv s₀ c c s) (tail : List Instr) {Q : State → Prop}
    (hQ : ∀ t, Inv s₀ (c+(b::bs).length) c t → t.gpr = s.gpr → WP isa (.block tail) t Q) :
    WP isa (.seq (.block (Impl.AesCfb.AArch64.Decrypt.inputs (b::bs)))
      (.seq (aes (b::bs))
        (.block (Impl.AesCfb.AArch64.Decrypt.finishData (b::bs) 0 ++ tail)))) s Q := by
  have hc' : c+bs.length+1 ≤ N s₀ := by simp only [List.length_cons] at hc; omega
  refine WP.seq (WP.mono (inputs_ok b bs s hbr.1 (by simp only [List.length_cons] at hlen; omega)
    (fun k hk => by
      rw [hI.x2, Offset.add_add_eq (Dp s₀) (show 16*c+16*k=16*(c+k) by omega)]
      exact ⟨dataR s₀, List.mem_append_right _ (by rw [hI.wr,hp.wr]; simp),
        Offset.contains_base _ (by simp only [List.length_cons] at hc; omega)
          (by have := hp.data_wrap; omega)⟩)) fun u ⟨hfirst,hload,fl⟩ => ?_)
  have hku := hI.keys.of_v hbr fl.v (fl.gpr _ (by simp)) (fl.gpr _ (by simp))
  have hinput : ∀ k (hk : k < (b::bs).length), u.v (b::bs)[k] = chaining s₀ (c+k) := by
    intro k hk
    cases k with
    | zero => simpa only [List.getElem_cons_zero,Nat.add_zero] using hfirst.trans hI.chain
    | succ k =>
      have hk' : k < bs.length := by simpa using hk
      rw [List.getElem_cons_succ,hload k (by simpa using hk),hI.x2,
        Offset.add_add_eq (Dp s₀) (show 16*c+16*k=16*(c+k) by omega),
        original_word hI.data (by omega) (by simp only [List.length_cons] at hc; omega)]
      rfl
  refine WP.seq (WP.mono (aes_ok hbr hku) fun v ⟨ha,fa⟩ => ?_)
  have hg : v.gpr = s.gpr := by funext r; rw [fa.gpr,fl.gpr r (by simp)]
  have hm : v.mem = s.mem := fa.mem.trans fl.mem
  have hv : v.v .v31 = chaining s₀ c := by rw [fa.v _ h31,fl.v _ h31,hI.chain]
  have hkv := hku.of_frame fa hbr
  rw [WP.block_append_iff]
  refine WP.mono (finishData_ok (m₀ := s₀.mem) (D := Dp s₀) (n := N s₀) (c := c)
    (F := output s₀) (chain := chaining s₀) (by have := hp.data_wrap; omega)
    (fun _ _ => rfl) (b::bs) 0 v hbr.1 h31 hbr.v16 (hg ▸ hI.x2) (by omega) (by simpa using hc)
    (by rw [fa.wr,fl.wr,hI.wr,hp.wr]; simp) (by simpa only [Nat.add_zero,hm] using hI.data)
    (by simpa using hv) (fun k hk i hi => by
      have hval := congrArg (fun a : Spec.Aes.State => a.getD i 0) (ha _ (List.getElem_mem hk))
      rw [getD_st _ hi,hinput k hk] at hval
      rw [hval]
      exact (getD_ofFn (f := fun i =>
        (Spec.Aes.cipher (R s₀) (wK s₀) (st (chaining s₀ (c+k)))).getD i.1 0 ^^^
          vbyte (s₀.mem.readW (blk s₀ (c+k)) 128) i.1) hi).symm))
    fun t ⟨hd,hchain,hframe,hg',_,hrd,hwr,ho⟩ => ?_
  have hkall : BlockRegs (.v31 :: b::bs) :=
    ⟨List.nodup_cons.mpr ⟨h31,hbr.1⟩,fun r hr => by
      rcases List.mem_cons.mp hr with hr | hr
      · subst r
        exact ⟨by decide,by decide,by decide,by decide,by decide,by decide,by decide,
          by decide,by decide,by decide,by decide,by decide,by decide,by decide,by decide⟩
      · exact hbr.2 r hr⟩
  have hkt := hkv.of_v hkall (fun r hr => ho r (fun h => hr (h ▸ List.mem_cons_self))
    (fun h => hr (List.mem_cons_of_mem _ h))) (by rw [hg']) (by rw [hg'])
  refine hQ t ⟨hc,hkt,?_,?_,?_,?_,?_,?_,?_,?_⟩ (hg'.trans hg)
  · rw [hg',hg]; exact hI.x2
  · rw [hg',hg]; exact hI.x3
  · rw [hg',hg]; exact hI.x11
  · simpa using hchain
  · simpa using hd
  · rw [hm] at hframe; exact hI.frame.trans hframe
  · rw [hrd,fa.rd,fl.rd]; exact hI.rd
  · rw [hwr,fa.wr,fl.wr]; exact hI.wr

end VG.Proof.AesCfb.AArch64.Decrypt
