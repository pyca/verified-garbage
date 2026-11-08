module

public import VerifiedGarbage.Proof.Scrypt.X86_64.PackedStore
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Sse

-- separate module: cache the 30-second half-block composition proof while iterating on loop metadata.

@[expose] public section
namespace VG.Proof.Scrypt.X86_64.Packed
open VG VG.X86_64 VG.Impl.Scrypt.X86_64.Packed
open VG.Spec.Scrypt (Word)
open VG.Proof.Scrypt.X86_64.Retained (memWords)

attribute [local irreducible] run storeMem

theorem Holds.keep {v : Vector Word 16} {s t : State} (h : Holds v s)
 (hk : ∀ r, r<4 → t.xmm (row r)=s.xmm (row r)) : Holds v t := by
 intro r hr q hq
 rw [dw,hk r hr]
 exact h r hr q hq

theorem load_ok {s : State} (hi : InRegions (s.rd++s.wr) (s.gpr .r15) 64) :
 WP isa (.block load) s fun t => F s t ∧ Holds (memWords s.mem (s.gpr .r15)) t := by
 unfold load
 rw [List.append_assoc,WP.block_append_iff]
 refine WP.mono (natural_load (by exact plus_zero _) hi) fun a ⟨fa,na,_⟩ => ?_
 refine block_run (by decide) a ?_
 rw [run_append]
 exact ⟨fa.trans ((run_frame (pack.map .xop) a).trans
  (run_frame retain (run (pack.map .xop) a))),retain_holds (pack_correct na)⟩

theorem absorb_ok {v : Vector Word 16} {s : State} {off : Nat} {p : Addr}
 (h : Holds v s) (hb : plus (s.gpr .rbx) off=p) (hi : InRegions (s.rd++s.wr) p 64) :
 WP isa (.block (absorb off)) s fun t =>
  Holds (v.zipWith (· ^^^ ·) (memWords s.mem p)) t ∧
  PackedValues savedInput (v.zipWith (· ^^^ ·) (memWords s.mem p)) t ∧ F s t := by
 unfold absorb
 rw [List.append_assoc,List.append_assoc,WP.block_append_iff]
 refine WP.mono (natural_load hb hi) fun a ⟨fa,na,ka⟩ => ?_
 have hv : Holds v a := h.keep fun r hr => by
  rcases cases4 hr with rfl|rfl|rfl|rfl
  all_goals exact ka _ (by decide) (by decide) (by decide) (by decide)
 have hp : Holds v (run (pack.map .xop) a) := hv.keep fun r hr => by
  rcases cases4 hr with rfl|rfl|rfl|rfl
  all_goals exact pack_keep _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
 have hx := xorState_holds hp (pack_correct na)
 have hs := saveInput_holds hx
 refine block_run (by decide) a ?_
 simp only [run_append]
 exact ⟨hs.1,hs.2,fa.trans ((run_frame (pack.map .xop) a).trans
  ((run_frame xorState (run (pack.map .xop) a)).trans
   (run_frame saveInput (run xorState (run (pack.map .xop) a)))))⟩

theorem rounds_input {v x : Vector Word 16} {s : State}
 (hv : Holds v s) (hx : PackedValues savedInput x s) (n : Nat) :
 WP isa (rounds n) s fun t => Holds (Nat.repeat Spec.Scrypt.doubleRound n v) t ∧
  PackedValues savedInput x t ∧ F s t :=
 WP.mono (rounds_ok hv n) fun t ⟨hv,ft,kt⟩ => ⟨hv,fun r hr q hq => by
  have ke : t.xmm (savedInput r)=s.xmm (savedInput r) := by
   rcases cases4 hr with rfl|rfl|rfl|rfl
   all_goals exact kt _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [dw,ke]
  exact hx r hr q hq,ft⟩

theorem store_ok {v : Vector Word 16} {s : State} {b : Reg} {p : Addr}
 (h : Holds v s) (hb : s.gpr b=p) (hi : InRegions s.wr p 64) :
 WP isa (.block (store b)) s fun t =>
  Holds v t ∧ memWords t.mem p=v ∧ Frame [VG.Proof.Scrypt.X86_64.bR p] s.mem t.mem ∧
  t.gpr=s.gpr ∧ t.rd=s.rd ∧ t.wr=s.wr := by
 unfold store
 rw [WP.block_append_iff]
 refine block_run (by decide) s ?_
 let a := run (unpack.map .xop) s
 have fa : F s a := run_frame _ _
 have hn : Natural outputReg v a := unpack_correct h
 have hh : Holds v a := h.keep fun r hr => by
  rcases cases4 hr with rfl|rfl|rfl|rfl
  all_goals exact unpack_keep _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
 exact WP.mono (stores_ok (b:=b) (by rw [fa.gpr,hb]) (by rw [fa.wr]; exact hi)) fun t ht => by
  subst t
  exact ⟨hh,storeMem_words hn _ _,by rw [← fa.mem]; exact storeMem_frame _ _ _,fa.gpr,fa.rd,fa.wr⟩

theorem half_ok {v : Vector Word 16} {s : State} {off : Nat} {src dst : Addr} {b : Reg}
 (h : Holds v s) (hs : plus (s.gpr .rbx) off=src) (hi : InRegions (s.rd++s.wr) src 64)
 (hb : s.gpr b=dst) (hw : InRegions s.wr dst 64) :
 WP isa (half off b) s fun t =>
  Holds (Spec.Scrypt.core (v.zipWith (· ^^^ ·) (memWords s.mem src))) t ∧
  memWords t.mem dst=Spec.Scrypt.core (v.zipWith (· ^^^ ·) (memWords s.mem src)) ∧
  Frame [VG.Proof.Scrypt.X86_64.bR dst] s.mem t.mem ∧
  t.gpr=s.gpr ∧ t.rd=s.rd ∧ t.wr=s.wr := by
 refine WP.seq (WP.mono (absorb_ok h hs hi) fun a ⟨ha,xa,fa⟩ => ?_)
 refine WP.seq (WP.mono (rounds_input ha xa 4) fun c ⟨hc,xc,fc⟩ => ?_)
 rw [WP.block_append_iff]
 refine block_run (by decide) c ?_
 let d := run finish c
 have fd : F c d := run_frame _ _
 have hd : Holds (Spec.Scrypt.core (v.zipWith (· ^^^ ·) (memWords s.mem src))) d := finish_holds hc xc
 exact WP.mono (store_ok hd (by rw [fd.gpr,fc.gpr,fa.gpr,hb])
   (by rw [fd.wr,fc.wr,fa.wr]; exact hw)) fun t ht =>
  ⟨ht.1,ht.2.1,by rw [fd.mem,fc.mem,fa.mem] at ht; exact ht.2.2.1,
   ht.2.2.2.1.trans (fd.gpr.trans (fc.gpr.trans fa.gpr)),
   ht.2.2.2.2.1.trans (fd.rd.trans (fc.rd.trans fa.rd)),
   ht.2.2.2.2.2.trans (fd.wr.trans (fc.wr.trans fa.wr))⟩

end VG.Proof.Scrypt.X86_64.Packed
