import VerifiedGarbage.Proof.Bignum.X86_64.AdxTri8Clear
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRect8Frame
import VerifiedGarbage.Proof.Bignum.X86_64.OpAt

namespace VG.Proof.Bignum.X86_64.AdxTri8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

theorem setup_ok {s : State} {B : Addr} {Z w a I : Nat}
    (hs : Scr s B Z) (hd : s.gpr .rdi=B) (hZ : slot w 8≤Z)
    {ps : List (Nat × Nat)} (hv : Ops s.mem B w ps) {ca : Nat} (pa : (ca, a) ∈ ps)
    (hI : word s.mem B (8*sFn 12)=BitVec.ofNat 64 I) :
    WP isa (.block (AdxTri8.setup ca)) s fun t =>
      t.gpr .rbp=off B (slot w a+8*I) ∧ t.mem=s.mem ∧ Keep [.rax,.rbp] s t := by
  have ld : ∀ k<32, InRegions (s.rd++s.wr) (off B (8*k)) 8 := fun k hk =>
    hs.ld (by have := hdr_lt_slot w 8 hk; omega)
  have add : off B (slot w a)+BitVec.ofNat 64 (8*I)=off B (slot w a+8*I) := off_off ..
  refine WP.mono (WP.keep [.rax,.rbp] (Q := fun t => t.gpr .rbp=off B (slot w a+8*I) ∧ t.mem=s.mem) ?_ rfl)
    fun t ⟨⟨p,m⟩,k⟩ => ⟨p,m,k⟩
  unfold AdxTri8.setup
  xrun [State.ea,hdr,hd,hdrOff,ld (sArr ca) (by have := hv.lt pa; unfold sArr; omega),ld (sFn 12) (by decide),
    show word s.mem B (8*sArr ca) = _ from hv.at pa,hI,AdxRect8.shift3,add]

theorem block_ok {s : State} {B : Addr} {Z w a I : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hd : s.gpr .rdi=B) (hh : Hdr s.mem B w mi) (hZ : slot w 8≤Z)
    {ps : List (Nat × Nat)} (hv : Ops s.mem B w ps) {ca : Nat} (pa : (ca, a) ∈ ps)
    (ha : a<8) (ha1 : a≠aAcc) (ha2 : a≠aTmp) (hIndex : I+8≤w)
    (hI : word s.mem B (8*sFn 12)=BitVec.ofNat 64 I) :
    WP isa (AdxTri8.block ca) s fun t =>
      2^64*wv t.mem B (output w I 0) 14=AdxSquare.crossValue s.mem B (slot w a+8*I) 8 ∧
      Outside B (output w I 0) 112 s.mem t.mem ∧ Keep mmRegs s t := by
  have ar := AdxRect8.tile_ranges hIndex hIndex ha ha1 ha2
  have outZ : output w I 0+112≤Z := by unfold output at *; omega
  unfold AdxTri8.block
  refine WP.seq (WP.mono (setup_ok hs hd hZ hv pa hI) fun u ⟨pu,mu,ku⟩ => ?_)
  refine WP.seq (WP.mono (clear_ok AdxTri8.columns u) fun v ⟨zv,mv,kv⟩ => ?_)
  have kuv := ku.trans kv
  have vz : value v AdxTri8.columns=0 := value_zero zv
  refine WP.mono (rows_ok 7 (hs.congr kuv.2.2) ((kuv.gpr (by decide)).trans hd) (mv ▸ mu ▸ hh) hZ
    (mv ▸ mu ▸ hI) ((kv.gpr (by decide)).trans pu) (by omega)
    (by simpa only [show 16*7=112 from rfl] using outZ)
    (by unfold output; omega) columns_regs (by decide) (value_zero_lt zv 7))
    fun t ⟨vt,ot,kt⟩ => ?_
  rw [vz,Nat.zero_add,mv,mu] at vt
  rw [mv,mu] at ot
  refine ⟨?_,ot,(kuv.trans kt).mono (by decide)⟩
  rw [vt,rowSum_cross]

end VG.Proof.Bignum.X86_64.AdxTri8
