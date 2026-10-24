module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.ImportData
public import VerifiedGarbage.Proof.Bignum.AArch64.PubSetup
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! Complete native context import starts with uninitialized scratch. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

def importRanges (w : Nat) : List (Nat × Nat) := [(8*sW,8),(8*sArr 0,64)]++importDataRanges w

theorem importPrefix_ok {s : State} {B ctx : Addr} {Z w k P : Nat}
 (scratch : Scr s B Z) (base : s.gpr .x0=B) (room : slot w 8≤Z)
 (words : w=(k+7)/8) (positive : 0<k) (size : k<2^31)
 (length : word s.mem B (8*sLen)=BitVec.ofNat 64 k) (context : word s.mem B (8*sCtx)=ctx)
 (readable : ∀ i<2*w,InRegions (s.rd++s.wr) (off ctx (24+8*i)) 8)
 (outside : ∀ i<16*w,Z≤ofs B (off ctx 24+BitVec.ofNat 64 i))
 (modulus : wv s.mem ctx 24 w=P) (r2 : wv s.mem ctx (24+8*w) w=2^(128*w)%P) (odd : P%2=1) :
 WP isa importPrefix s fun t =>
 ∃ mi,Good t B Z w mi ∧ wv t.mem B (slot w 0) w=P ∧
 ((word t.mem B (slot w 0)).toNat*mi.toNat+1)%2^64=0 ∧
 wv t.mem B (slot w 4) w=2^(128*w)%P ∧ Frm B (importRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
 unfold importPrefix
 simp only [seqs]
 rw [WP.seq_iff]
 refine WP.mono (head_ok scratch base (by rw [←words];exact room) (by omega)
  (by change word s.mem B (8*Public.sK)=_;exact length)) ?_
 rintro a ⟨_,width,arrays,frameA,restA⟩
 rw [←words] at width arrays
 have goodA : Good a B Z w (word a.mem B (8*sMinv)) :=
  ⟨scratch.congr restA.wr,(restA.gpr .x0 (by decide)).trans base,width,rfl,arrays⟩
 have inscrA : InScr B Z s.mem a.mem :=
  InScr.of_frm (frameA.mono (by simp [pcLoadRanges])) (fun r hr =>Nat.le_trans (pcLoadRanges_le w r hr) room)
 have contextA : word a.mem B (8*sCtx)=ctx := by
  rw [frameA.word_eq (by
   simp only [List.mem_cons,List.not_mem_nil,or_false]
   rintro _ (rfl|rfl) <;> decide) (by decide)]
  exact context
 have prefixValue (d : Nat) (bound : d+8*w≤24+16*w) (lower : 24≤d) : wv a.mem ctx d w=wv s.mem ctx d w := by
  apply wv_congr
  intro i hi
  apply Mem.readW_congr
  intro b hb
  apply inscrA
  have sep := outside (d-24+8*i+b) (by omega)
  have eq : off ctx (d+8*i)+BitVec.ofNat 64 b=off ctx 24+BitVec.ofNat 64 (d-24+8*i+b) := by
   unfold off
   rw [BitVec.add_assoc,←BitVec.ofNat_add,BitVec.add_assoc,←BitVec.ofNat_add]
   congr 2
   omega
  rw [eq]
  exact sep
 change WP isa importData a _
 refine WP.mono (importData_ok goodA room (by rw [words];omega) (by rw [words];omega) contextA
  (fun i hi =>by rw [restA.rd,restA.wr];exact readable i hi) outside
  ((prefixValue 24 (by omega) (by omega)).trans modulus)
  ((prefixValue (24+8*w) (by omega) (by omega)).trans r2) odd) ?_
 rintro t ⟨mi,good,modulusT,inverseT,r2T,frameT,restT⟩
 exact ⟨mi,good,modulusT,inverseT,r2T,
  (frameA.mono (fun r hr =>List.mem_append_left _ hr)).trans
   (frameT.mono (fun r hr =>List.mem_append_right _ hr)),(restA.trans restT).mono (by simp [mmRegs])⟩

end VG.Proof.Ffdh.AArch64.Cached
