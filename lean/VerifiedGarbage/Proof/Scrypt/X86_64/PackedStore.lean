module

public import VerifiedGarbage.Proof.Scrypt.X86_64.PackedMemory
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Reduce
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.Offset

-- separate module: isolate vector-to-memory store proofs from the slower half-block composition proof.

@[expose] public section
namespace VG.Proof.Scrypt.X86_64.Packed
open VG VG.X86_64 VG.Impl.Scrypt.X86_64.Packed
open VG.Spec.Scrypt (Word)
open VG.Proof.Scrypt.X86_64.Retained (memWords)

theorem range4 : List.range 4 = [0,1,2,3] := rfl

theorem retain_holds {v : Vector Word 16} {s : State} (h : PackedValues packedReg v s) :
 Holds v (run retain s) := by
 intro r hr q hq
 have hh := h r hr q hq
 rcases cases4 hr with rfl|rfl|rfl|rfl
 all_goals simpa only [retain,range4,List.map_cons,List.map_nil,run,dw,row,packedReg,xmm_bin,
  reduceCtorEq,↓reduceIte,eval_movdqa] using hh

theorem xorState_holds {v x : Vector Word 16} {s : State}
 (hv : Holds v s) (hx : PackedValues packedReg x s) :
 Holds (v.zipWith (· ^^^ ·) x) (run xorState s) := by
 intro r hr q hq
 have hvv := hv r hr q hq
 have hxx := hx r hr q hq
 rcases cases4 hr with rfl|rfl|rfl|rfl
 all_goals simp only [xorState,range4,List.map_cons,List.map_nil,run,dw,row,packedReg,xmm_bin,
  reduceCtorEq,↓reduceIte,index]
 all_goals simp only [dw,row,packedReg,index] at hvv hxx
 all_goals rw [dword_pxor,Vector.getElem_zipWith (Nat.mod_lt _ (by decide)),← hvv,← hxx]

theorem saveInput_holds {v : Vector Word 16} {s : State} (h : Holds v s) :
 Holds v (run saveInput s) ∧ PackedValues savedInput v (run saveInput s) := by
 constructor <;> intro r hr q hq
 all_goals have hh := h r hr q hq
 all_goals rcases cases4 hr with rfl|rfl|rfl|rfl
 all_goals simpa only [saveInput,range4,List.map_cons,List.map_nil,run,dw,row,savedInput,xmm_bin,
  reduceCtorEq,↓reduceIte,eval_movdqa] using hh

theorem finish_holds {v x : Vector Word 16} {s : State}
 (hv : Holds v s) (hx : PackedValues savedInput x s) :
 Holds (v.zipWith (· + ·) x) (run finish s) := by
 intro r hr q hq
 have hvv := hv r hr q hq
 have hxx := hx r hr q hq
 rcases cases4 hr with rfl|rfl|rfl|rfl
 all_goals simp only [finish,range4,List.map_cons,List.map_nil,run,dw,row,savedInput,xmm_bin,
  reduceCtorEq,↓reduceIte,index]
 all_goals simp only [dw,row,savedInput,index] at hvv hxx
 all_goals rw [dword_paddd _ _ hq,Vector.getElem_zipWith (Nat.mod_lt _ (by decide)),← hvv,← hxx]

def storeMem (m : Mem) (p : Addr) (s : State) : Mem :=
 (((m.writeW (plus p 0) (s.xmm (outputReg 0))).writeW
  (plus p 16) (s.xmm (outputReg 1))).writeW
  (plus p 32) (s.xmm (outputReg 2))).writeW (plus p 48) (s.xmm (outputReg 3))

theorem store_row_same (m : Mem) (p : Addr) (r : Nat) (v : BitVec 128) {q : Nat} (hq : q<4) :
 (m.writeW (plus p (16*r)) v).readW (plus p (16*r+4*q)) 32 = dword v q := by
 have e : plus p (16*r+4*q) = plus p (16*r)+BitVec.ofNat 64 (4*q) := by
  simp only [plus,BitVec.ofNat_add,BitVec.add_assoc]
 rw [e,readW_writeW128 _ _ _ hq]

theorem store_row_other (m : Mem) (p : Addr) {r k q : Nat}
 (hr : r<4) (hk : k<4) (hq : q<4) (h : r≠k) (v : BitVec 128) :
 (m.writeW (plus p (16*r)) v).readW (plus p (16*k+4*q)) 32 =
 m.readW (plus p (16*k+4*q)) 32 :=
 Mem.readW_writeW_sep (Offset.sep p (by omega) (by omega) (by omega)) (by decide)

theorem storeMem_read (m : Mem) (p : Addr) (s : State) {r q : Nat} (hr : r<4) (hq : q<4) :
 (storeMem m p s).readW (plus p (16*r+4*q)) 32 = dw s (outputReg r) q := by
 rcases cases4 hr with rfl|rfl|rfl|rfl
 all_goals unfold storeMem
 · rw [store_row_other _ _ (r:=3) (by decide) (by decide) hq (by decide),
   store_row_other _ _ (r:=2) (by decide) (by decide) hq (by decide),
   store_row_other _ _ (r:=1) (by decide) (by decide) hq (by decide),store_row_same _ p 0 _ hq]
 · rw [store_row_other _ _ (r:=3) (by decide) (by decide) hq (by decide),
   store_row_other _ _ (r:=2) (by decide) (by decide) hq (by decide),store_row_same _ p 1 _ hq]
 · rw [store_row_other _ _ (r:=3) (by decide) (by decide) hq (by decide),store_row_same _ p 2 _ hq]
 · exact store_row_same _ p 3 _ hq

theorem storeMem_words {v : Vector Spec.Scrypt.Word 16} {s : State}
 (h : Natural outputReg v s) (m : Mem) (p : Addr) : memWords (storeMem m p s) p = v := by
 apply Vector.ext
 intro j hj
 have eqj : 16*(j/4)+4*(j%4)=4*j := by omega
 have hr : j/4<4 := by omega
 have hq : j%4<4 := Nat.mod_lt _ (by decide)
 have ee := storeMem_read m p s hr hq
 rw [eqj,h _ hr _ hq] at ee
 have ej : 4*(j/4)+j%4=j := by omega
 simpa only [memWords,Vector.getElem_ofFn,bufAt,ofInt_natCast,ej] using ee

theorem wp_store128 {s : State} {r : XReg} {m : MemOp} {p : Addr} {is : List Instr} {Q : State → Prop}
 (ha : s.ea m = p) (hi : InRegions s.wr p 16)
 (k : WP isa (.block is) {s with mem := s.mem.writeW p (s.xmm r)} Q) :
 WP isa (.block (.movdquStore m r :: is)) s Q := by
 refine WP.block_cons_iff.mpr ⟨_,?_,k⟩
 simp only [reduceExec,State.store128,ha,hi,ite_true]

theorem stores_ok {s : State} {b : Reg} {p : Addr}
 (hb : s.gpr b = p) (hi : InRegions s.wr p 64) :
 WP isa (.block ((List.range 4).map (fun k => .movdquStore (VG.Impl.Scrypt.X86_64.at_ b (16*k)) (outputReg k)))) s
  fun t => t = {s with mem := storeMem s.mem p s} := by
 have addr (m : Mem) (k : Nat) : ({s with mem:=m} : State).ea (VG.Impl.Scrypt.X86_64.at_ b (16*k)) = plus p (16*k) := by
  rw [ea_at]; exact congrArg (fun a => plus a (16*k)) hb
 rw [range4]
 simp only [List.map_cons,List.map_nil]
 refine wp_store128 (by rw [ea_at,hb]) (access hi (by decide)) ?_
 refine wp_store128 (addr _ 1) (access hi (by decide)) ?_
 refine wp_store128 (addr _ 2) (access hi (by decide)) ?_
 refine wp_store128 (addr _ 3) (access hi (by decide)) ?_
 exact WP.block_nil rfl

theorem storeMem_frame (m : Mem) (p : Addr) (s : State) :
 Frame [VG.Proof.Scrypt.X86_64.bR p] m (storeMem m p s) := by
 unfold storeMem
 have part (k : Nat) (hk : k<4) : (VG.Proof.Scrypt.X86_64.bR p).Contains (plus p (16*k)) 16 :=
  Offset.contains_base p (by omega) (by omega)
 exact ((((Frame.refl _ _).writeW (by simp) _ (part 0 (by decide))).writeW
  (by simp) _ (part 1 (by decide))).writeW (by simp) _ (part 2 (by decide))).writeW
  (by simp) _ (part 3 (by decide))

end VG.Proof.Scrypt.X86_64.Packed
