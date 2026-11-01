// The functions of `src/internal/vg_mldsa_ntt.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_ntt:
	movz w9, #65024, lsl #0
	movk w9, #63, lsl #16
	str w9, [x1, #0]
	movz w9, #25847, lsl #0
	movk w9, #0, lsl #16
	str w9, [x1, #4]
	movz w9, #4355, lsl #0
	movk w9, #88, lsl #16
	str w9, [x1, #8]
	movz w9, #62724, lsl #0
	movk w9, #119, lsl #16
	str w9, [x1, #12]
	movz w9, #40516, lsl #0
	movk w9, #3, lsl #16
	str w9, [x1, #16]
	movz w9, #281, lsl #0
	movk w9, #116, lsl #16
	str w9, [x1, #20]
	movz w9, #33065, lsl #0
	movk w9, #114, lsl #16
	str w9, [x1, #24]
	movz w9, #7716, lsl #0
	movk w9, #7, lsl #16
	str w9, [x1, #28]
	movz w9, #56875, lsl #0
	movk w9, #27, lsl #16
	str w9, [x1, #32]
	movz w9, #59691, lsl #0
	movk w9, #35, lsl #16
	str w9, [x1, #36]
	movz w9, #25774, lsl #0
	movk w9, #122, lsl #16
	str w9, [x1, #40]
	movz w9, #62592, lsl #0
	movk w9, #95, lsl #16
	str w9, [x1, #44]
	movz w9, #39541, lsl #0
	movk w9, #47, lsl #16
	str w9, [x1, #48]
	movz w9, #56074, lsl #0
	movk w9, #83, lsl #16
	str w9, [x1, #52]
	movz w9, #31305, lsl #0
	movk w9, #47, lsl #16
	str w9, [x1, #56]
	movz w9, #58663, lsl #0
	movk w9, #40, lsl #16
	str w9, [x1, #60]
	movz w9, #38488, lsl #0
	movk w9, #41, lsl #16
	str w9, [x1, #64]
	movz w9, #41072, lsl #0
	movk w9, #15, lsl #16
	str w9, [x1, #68]
	movz w9, #26021, lsl #0
	movk w9, #111, lsl #16
	str w9, [x1, #72]
	movz w9, #46984, lsl #0
	movk w9, #54, lsl #16
	str w9, [x1, #76]
	movz w9, #32145, lsl #0
	movk w9, #119, lsl #16
	str w9, [x1, #80]
	movz w9, #51873, lsl #0
	movk w9, #110, lsl #16
	str w9, [x1, #84]
	movz w9, #63848, lsl #0
	movk w9, #39, lsl #16
	str w9, [x1, #88]
	movz w9, #45948, lsl #0
	movk w9, #95, lsl #16
	str w9, [x1, #92]
	movz w9, #36311, lsl #0
	movk w9, #95, lsl #16
	str w9, [x1, #96]
	movz w9, #64232, lsl #0
	movk w9, #68, lsl #16
	str w9, [x1, #100]
	movz w9, #34040, lsl #0
	movk w9, #106, lsl #16
	str w9, [x1, #104]
	movz w9, #56473, lsl #0
	movk w9, #77, lsl #16
	str w9, [x1, #108]
	movz w9, #53301, lsl #0
	movk w9, #26, lsl #16
	str w9, [x1, #112]
	movz w9, #37923, lsl #0
	movk w9, #127, lsl #16
	str w9, [x1, #116]
	movz w9, #12801, lsl #0
	movk w9, #61, lsl #16
	str w9, [x1, #120]
	movz w9, #17861, lsl #0
	movk w9, #4, lsl #16
	str w9, [x1, #124]
	movz w9, #19047, lsl #0
	movk w9, #41, lsl #16
	str w9, [x1, #128]
	movz w9, #30240, lsl #0
	movk w9, #1, lsl #16
	str w9, [x1, #132]
	movz w9, #62669, lsl #0
	movk w9, #46, lsl #16
	str w9, [x1, #136]
	movz w9, #57029, lsl #0
	movk w9, #53, lsl #16
	str w9, [x1, #140]
	movz w9, #34052, lsl #0
	movk w9, #102, lsl #16
	str w9, [x1, #144]
	movz w9, #4141, lsl #0
	movk w9, #73, lsl #16
	str w9, [x1, #148]
	movz w9, #10197, lsl #0
	movk w9, #89, lsl #16
	str w9, [x1, #152]
	movz w9, #48815, lsl #0
	movk w9, #59, lsl #16
	str w9, [x1, #156]
	movz w9, #62854, lsl #0
	movk w9, #68, lsl #16
	str w9, [x1, #160]
	movz w9, #28285, lsl #0
	movk w9, #81, lsl #16
	str w9, [x1, #164]
	movz w9, #35478, lsl #0
	movk w9, #54, lsl #16
	str w9, [x1, #168]
	movz w9, #7746, lsl #0
	movk w9, #84, lsl #16
	str w9, [x1, #172]
	movz w9, #1024, lsl #0
	movk w9, #54, lsl #16
	str w9, [x1, #176]
	movz w9, #19022, lsl #0
	movk w9, #123, lsl #16
	str w9, [x1, #180]
	movz w9, #54940, lsl #0
	movk w9, #35, lsl #16
	str w9, [x1, #184]
	movz w9, #42334, lsl #0
	movk w9, #119, lsl #16
	str w9, [x1, #188]
	movz w9, #62014, lsl #0
	movk w9, #101, lsl #16
	str w9, [x1, #192]
	movz w9, #51927, lsl #0
	movk w9, #102, lsl #16
	str w9, [x1, #196]
	movz w9, #32286, lsl #0
	movk w9, #53, lsl #16
	str w9, [x1, #200]
	movz w9, #36698, lsl #0
	movk w9, #69, lsl #16
	str w9, [x1, #204]
	movz w9, #33855, lsl #0
	movk w9, #53, lsl #16
	str w9, [x1, #208]
	movz w9, #13848, lsl #0
	movk w9, #95, lsl #16
	str w9, [x1, #212]
	movz w9, #29789, lsl #0
	movk w9, #103, lsl #16
	str w9, [x1, #216]
	movz w9, #29580, lsl #0
	movk w9, #56, lsl #16
	str w9, [x1, #220]
	movz w9, #25512, lsl #0
	movk w9, #12, lsl #16
	str w9, [x1, #224]
	movz w9, #7066, lsl #0
	movk w9, #8, lsl #16
	str w9, [x1, #228]
	movz w9, #36726, lsl #0
	movk w9, #14, lsl #16
	str w9, [x1, #232]
	movz w9, #14419, lsl #0
	movk w9, #59, lsl #16
	str w9, [x1, #236]
	movz w9, #34100, lsl #0
	movk w9, #59, lsl #16
	str w9, [x1, #240]
	movz w9, #56369, lsl #0
	movk w9, #88, lsl #16
	str w9, [x1, #244]
	movz w9, #40276, lsl #0
	movk w9, #31, lsl #16
	str w9, [x1, #248]
	movz w9, #12078, lsl #0
	movk w9, #85, lsl #16
	str w9, [x1, #252]
	movz w9, #59110, lsl #0
	movk w9, #67, lsl #16
	str w9, [x1, #256]
	movz w9, #35970, lsl #0
	movk w9, #104, lsl #16
	str w9, [x1, #260]
	movz w9, #49616, lsl #0
	movk w9, #71, lsl #16
	str w9, [x1, #264]
	movz w9, #30746, lsl #0
	movk w9, #81, lsl #16
	str w9, [x1, #268]
	movz w9, #46686, lsl #0
	movk w9, #105, lsl #16
	str w9, [x1, #272]
	movz w9, #2542, lsl #0
	movk w9, #53, lsl #16
	str w9, [x1, #276]
	movz w9, #13767, lsl #0
	movk w9, #33, lsl #16
	str w9, [x1, #280]
	movz w9, #44988, lsl #0
	movk w9, #103, lsl #16
	str w9, [x1, #284]
	movz w9, #44918, lsl #0
	movk w9, #108, lsl #16
	str w9, [x1, #288]
	movz w9, #38770, lsl #0
	movk w9, #29, lsl #16
	str w9, [x1, #292]
	movz w9, #36979, lsl #0
	movk w9, #65, lsl #16
	str w9, [x1, #296]
	movz w9, #40183, lsl #0
	movk w9, #112, lsl #16
	str w9, [x1, #300]
	movz w9, #12929, lsl #0
	movk w9, #79, lsl #16
	str w9, [x1, #304]
	movz w9, #45743, lsl #0
	movk w9, #79, lsl #16
	str w9, [x1, #308]
	movz w9, #28897, lsl #0
	movk w9, #72, lsl #16
	str w9, [x1, #312]
	movz w9, #61386, lsl #0
	movk w9, #1, lsl #16
	str w9, [x1, #316]
	movz w9, #4338, lsl #0
	movk w9, #52, lsl #16
	str w9, [x1, #320]
	movz w9, #56966, lsl #0
	movk w9, #112, lsl #16
	str w9, [x1, #324]
	movz w9, #50744, lsl #0
	movk w9, #32, lsl #16
	str w9, [x1, #328]
	movz w9, #28319, lsl #0
	movk w9, #41, lsl #16
	str w9, [x1, #332]
	movz w9, #38820, lsl #0
	movk w9, #82, lsl #16
	str w9, [x1, #336]
	movz w9, #33868, lsl #0
	movk w9, #71, lsl #16
	str w9, [x1, #340]
	movz w9, #39534, lsl #0
	movk w9, #121, lsl #16
	str w9, [x1, #344]
	movz w9, #5130, lsl #0
	movk w9, #90, lsl #16
	str w9, [x1, #348]
	movz w9, #41603, lsl #0
	movk w9, #117, lsl #16
	str w9, [x1, #352]
	movz w9, #8468, lsl #0
	movk w9, #109, lsl #16
	str w9, [x1, #356]
	movz w9, #34364, lsl #0
	movk w9, #127, lsl #16
	str w9, [x1, #360]
	movz w9, #59896, lsl #0
	movk w9, #107, lsl #16
	str w9, [x1, #364]
	movz w9, #3038, lsl #0
	movk w9, #122, lsl #16
	str w9, [x1, #368]
	movz w9, #38356, lsl #0
	movk w9, #20, lsl #16
	str w9, [x1, #372]
	movz w9, #17763, lsl #0
	movk w9, #28, lsl #16
	str w9, [x1, #376]
	movz w9, #3171, lsl #0
	movk w9, #106, lsl #16
	str w9, [x1, #380]
	movz w9, #56298, lsl #0
	movk w9, #76, lsl #16
	str w9, [x1, #384]
	movz w9, #2800, lsl #0
	movk w9, #4, lsl #16
	str w9, [x1, #388]
	movz w9, #50199, lsl #0
	movk w9, #7, lsl #16
	str w9, [x1, #392]
	movz w9, #17800, lsl #0
	movk w9, #47, lsl #16
	str w9, [x1, #396]
	movz w9, #44288, lsl #0
	movk w9, #0, lsl #16
	str w9, [x1, #400]
	movz w9, #5823, lsl #0
	movk w9, #111, lsl #16
	str w9, [x1, #404]
	movz w9, #52548, lsl #0
	movk w9, #13, lsl #16
	str w9, [x1, #408]
	movz w9, #26458, lsl #0
	movk w9, #60, lsl #16
	str w9, [x1, #412]
	movz w9, #3019, lsl #0
	movk w9, #71, lsl #16
	str w9, [x1, #416]
	movz w9, #48767, lsl #0
	movk w9, #127, lsl #16
	str w9, [x1, #420]
	movz w9, #14664, lsl #0
	movk w9, #25, lsl #16
	str w9, [x1, #424]
	movz w9, #18881, lsl #0
	movk w9, #78, lsl #16
	str w9, [x1, #428]
	movz w9, #30060, lsl #0
	movk w9, #36, lsl #16
	str w9, [x1, #432]
	movz w9, #42976, lsl #0
	movk w9, #124, lsl #16
	str w9, [x1, #436]
	movz w9, #39073, lsl #0
	movk w9, #11, lsl #16
	str w9, [x1, #440]
	movz w9, #51209, lsl #0
	movk w9, #107, lsl #16
	str w9, [x1, #444]
	movz w9, #58476, lsl #0
	movk w9, #2, lsl #16
	str w9, [x1, #448]
	movz w9, #43017, lsl #0
	movk w9, #73, lsl #16
	str w9, [x1, #452]
	movz w9, #14018, lsl #0
	movk w9, #48, lsl #16
	str w9, [x1, #456]
	movz w9, #40951, lsl #0
	movk w9, #99, lsl #16
	str w9, [x1, #460]
	movz w9, #7316, lsl #0
	movk w9, #91, lsl #16
	str w9, [x1, #464]
	movz w9, #10977, lsl #0
	movk w9, #125, lsl #16
	str w9, [x1, #468]
	movz w9, #4869, lsl #0
	movk w9, #20, lsl #16
	str w9, [x1, #472]
	movz w9, #30610, lsl #0
	movk w9, #20, lsl #16
	str w9, [x1, #476]
	movz w9, #40485, lsl #0
	movk w9, #19, lsl #16
	str w9, [x1, #480]
	movz w9, #45281, lsl #0
	movk w9, #103, lsl #16
	str w9, [x1, #484]
	movz w9, #31045, lsl #0
	movk w9, #115, lsl #16
	str w9, [x1, #488]
	movz w9, #59395, lsl #0
	movk w9, #105, lsl #16
	str w9, [x1, #492]
	movz w9, #52899, lsl #0
	movk w9, #81, lsl #16
	str w9, [x1, #496]
	movz w9, #42909, lsl #0
	movk w9, #68, lsl #16
	str w9, [x1, #500]
	movz w9, #32856, lsl #0
	movk w9, #72, lsl #16
	str w9, [x1, #504]
	movz w9, #38873, lsl #0
	movk w9, #58, lsl #16
	str w9, [x1, #508]
	movz w9, #60051, lsl #0
	movk w9, #31, lsl #16
	str w9, [x1, #512]
	movz w9, #65370, lsl #0
	movk w9, #51, lsl #16
	str w9, [x1, #516]
	movz w9, #22740, lsl #0
	movk w9, #35, lsl #16
	str w9, [x1, #520]
	movz w9, #16888, lsl #0
	movk w9, #58, lsl #16
	str w9, [x1, #524]
	movz w9, #57203, lsl #0
	movk w9, #76, lsl #16
	str w9, [x1, #528]
	movz w9, #15867, lsl #0
	movk w9, #34, lsl #16
	str w9, [x1, #532]
	movz w9, #35744, lsl #0
	movk w9, #90, lsl #16
	str w9, [x1, #536]
	movz w9, #33827, lsl #0
	movk w9, #73, lsl #16
	str w9, [x1, #540]
	movz w9, #4853, lsl #0
	movk w9, #4, lsl #16
	str w9, [x1, #544]
	movz w9, #9607, lsl #0
	movk w9, #37, lsl #16
	str w9, [x1, #548]
	movz w9, #1265, lsl #0
	movk w9, #109, lsl #16
	str w9, [x1, #552]
	movz w9, #39773, lsl #0
	movk w9, #53, lsl #16
	str w9, [x1, #556]
	movz w9, #10401, lsl #0
	movk w9, #74, lsl #16
	str w9, [x1, #560]
	movz w9, #33533, lsl #0
	movk w9, #70, lsl #16
	str w9, [x1, #564]
	movz w9, #39767, lsl #0
	movk w9, #109, lsl #16
	str w9, [x1, #568]
	movz w9, #9695, lsl #0
	movk w9, #79, lsl #16
	str w9, [x1, #572]
	movz w9, #48734, lsl #0
	movk w9, #13, lsl #16
	str w9, [x1, #576]
	movz w9, #24090, lsl #0
	movk w9, #28, lsl #16
	str w9, [x1, #580]
	movz w9, #57574, lsl #0
	movk w9, #13, lsl #16
	str w9, [x1, #584]
	movz w9, #32602, lsl #0
	movk w9, #12, lsl #16
	str w9, [x1, #588]
	movz w9, #36739, lsl #0
	movk w9, #7, lsl #16
	str w9, [x1, #592]
	movz w9, #17035, lsl #0
	movk w9, #103, lsl #16
	str w9, [x1, #596]
	movz w9, #14085, lsl #0
	movk w9, #127, lsl #16
	str w9, [x1, #600]
	movz w9, #59133, lsl #0
	movk w9, #119, lsl #16
	str w9, [x1, #604]
	movz w9, #57378, lsl #0
	movk w9, #117, lsl #16
	str w9, [x1, #608]
	movz w9, #15095, lsl #0
	movk w9, #80, lsl #16
	str w9, [x1, #612]
	movz w9, #132, lsl #0
	movk w9, #31, lsl #16
	str w9, [x1, #616]
	movz w9, #61318, lsl #0
	movk w9, #48, lsl #16
	str w9, [x1, #620]
	movz w9, #39294, lsl #0
	movk w9, #73, lsl #16
	str w9, [x1, #624]
	movz w9, #56535, lsl #0
	movk w9, #119, lsl #16
	str w9, [x1, #628]
	movz w9, #9619, lsl #0
	movk w9, #116, lsl #16
	str w9, [x1, #632]
	movz w9, #451, lsl #0
	movk w9, #73, lsl #16
	str w9, [x1, #636]
	movz w9, #14617, lsl #0
	movk w9, #5, lsl #16
	str w9, [x1, #640]
	movz w9, #24844, lsl #0
	movk w9, #4, lsl #16
	str w9, [x1, #644]
	movz w9, #44354, lsl #0
	movk w9, #90, lsl #16
	str w9, [x1, #648]
	movz w9, #45083, lsl #0
	movk w9, #62, lsl #16
	str w9, [x1, #652]
	movz w9, #29415, lsl #0
	movk w9, #52, lsl #16
	str w9, [x1, #656]
	movz w9, #57404, lsl #0
	movk w9, #76, lsl #16
	str w9, [x1, #660]
	movz w9, #31943, lsl #0
	movk w9, #26, lsl #16
	str w9, [x1, #664]
	movz w9, #6436, lsl #0
	movk w9, #3, lsl #16
	str w9, [x1, #668]
	movz w9, #24293, lsl #0
	movk w9, #43, lsl #16
	str w9, [x1, #672]
	movz w9, #4505, lsl #0
	movk w9, #41, lsl #16
	str w9, [x1, #676]
	movz w9, #23099, lsl #0
	movk w9, #88, lsl #16
	str w9, [x1, #680]
	movz w9, #19825, lsl #0
	movk w9, #19, lsl #16
	str w9, [x1, #684]
	movz w9, #57628, lsl #0
	movk w9, #61, lsl #16
	str w9, [x1, #688]
	movz w9, #2436, lsl #0
	movk w9, #19, lsl #16
	str w9, [x1, #692]
	movz w9, #61521, lsl #0
	movk w9, #37, lsl #16
	str w9, [x1, #696]
	movz w9, #23110, lsl #0
	movk w9, #24, lsl #16
	str w9, [x1, #700]
	movz w9, #25881, lsl #0
	movk w9, #70, lsl #16
	str w9, [x1, #704]
	movz w9, #5310, lsl #0
	movk w9, #19, lsl #16
	str w9, [x1, #708]
	movz w9, #14481, lsl #0
	movk w9, #40, lsl #16
	str w9, [x1, #712]
	movz w9, #48017, lsl #0
	movk w9, #73, lsl #16
	str w9, [x1, #716]
	movz w9, #12426, lsl #0
	movk w9, #82, lsl #16
	str w9, [x1, #720]
	movz w9, #34111, lsl #0
	movk w9, #28, lsl #16
	str w9, [x1, #724]
	movz w9, #2891, lsl #0
	movk w9, #29, lsl #16
	str w9, [x1, #728]
	movz w9, #54951, lsl #0
	movk w9, #111, lsl #16
	str w9, [x1, #732]
	movz w9, #35007, lsl #0
	movk w9, #107, lsl #16
	str w9, [x1, #736]
	movz w9, #57627, lsl #0
	movk w9, #18, lsl #16
	str w9, [x1, #740]
	movz w9, #15935, lsl #0
	movk w9, #77, lsl #16
	str w9, [x1, #744]
	movz w9, #3376, lsl #0
	movk w9, #106, lsl #16
	str w9, [x1, #748]
	movz w9, #64997, lsl #0
	movk w9, #120, lsl #16
	str w9, [x1, #752]
	movz w9, #1735, lsl #0
	movk w9, #20, lsl #16
	str w9, [x1, #756]
	movz w9, #29315, lsl #0
	movk w9, #50, lsl #16
	str w9, [x1, #760]
	movz w9, #60783, lsl #0
	movk w9, #97, lsl #16
	str w9, [x1, #764]
	movz w9, #22868, lsl #0
	movk w9, #108, lsl #16
	str w9, [x1, #768]
	movz w9, #16537, lsl #0
	movk w9, #29, lsl #16
	str w9, [x1, #772]
	movz w9, #1401, lsl #0
	movk w9, #89, lsl #16
	str w9, [x1, #776]
	movz w9, #58798, lsl #0
	movk w9, #106, lsl #16
	str w9, [x1, #780]
	movz w9, #58373, lsl #0
	movk w9, #22, lsl #16
	str w9, [x1, #784]
	movz w9, #56295, lsl #0
	movk w9, #11, lsl #16
	str w9, [x1, #788]
	movz w9, #7656, lsl #0
	movk w9, #34, lsl #16
	str w9, [x1, #792]
	movz w9, #63695, lsl #0
	movk w9, #51, lsl #16
	str w9, [x1, #796]
	movz w9, #39221, lsl #0
	movk w9, #119, lsl #16
	str w9, [x1, #800]
	movz w9, #43533, lsl #0
	movk w9, #84, lsl #16
	str w9, [x1, #804]
	movz w9, #24569, lsl #0
	movk w9, #102, lsl #16
	str w9, [x1, #808]
	movz w9, #45400, lsl #0
	movk w9, #99, lsl #16
	str w9, [x1, #812]
	movz w9, #28956, lsl #0
	movk w9, #88, lsl #16
	str w9, [x1, #816]
	movz w9, #3091, lsl #0
	movk w9, #71, lsl #16
	str w9, [x1, #820]
	movz w9, #4312, lsl #0
	movk w9, #9, lsl #16
	str w9, [x1, #824]
	movz w9, #15904, lsl #0
	movk w9, #70, lsl #16
	str w9, [x1, #828]
	movz w9, #9817, lsl #0
	movk w9, #97, lsl #16
	str w9, [x1, #832]
	movz w9, #7563, lsl #0
	movk w9, #37, lsl #16
	str w9, [x1, #836]
	movz w9, #29623, lsl #0
	movk w9, #37, lsl #16
	str w9, [x1, #840]
	movz w9, #23696, lsl #0
	movk w9, #125, lsl #16
	str w9, [x1, #844]
	movz w9, #56728, lsl #0
	movk w9, #29, lsl #16
	str w9, [x1, #848]
	movz w9, #26776, lsl #0
	movk w9, #51, lsl #16
	str w9, [x1, #852]
	movz w9, #54459, lsl #0
	movk w9, #2, lsl #16
	str w9, [x1, #856]
	movz w9, #29608, lsl #0
	movk w9, #109, lsl #16
	str w9, [x1, #860]
	movz w9, #19647, lsl #0
	movk w9, #79, lsl #16
	str w9, [x1, #864]
	movz w9, #31772, lsl #0
	movk w9, #2, lsl #16
	str w9, [x1, #868]
	movz w9, #43528, lsl #0
	movk w9, #24, lsl #16
	str w9, [x1, #872]
	movz w9, #64881, lsl #0
	movk w9, #45, lsl #16
	str w9, [x1, #876]
	movz w9, #23717, lsl #0
	movk w9, #12, lsl #16
	str w9, [x1, #880]
	movz w9, #14234, lsl #0
	movk w9, #25, lsl #16
	str w9, [x1, #884]
	movz w9, #33128, lsl #0
	movk w9, #71, lsl #16
	str w9, [x1, #888]
	movz w9, #27710, lsl #0
	movk w9, #100, lsl #16
	str w9, [x1, #892]
	movz w9, #33085, lsl #0
	movk w9, #81, lsl #16
	str w9, [x1, #896]
	movz w9, #50489, lsl #0
	movk w9, #53, lsl #16
	str w9, [x1, #900]
	movz w9, #277, lsl #0
	movk w9, #59, lsl #16
	str w9, [x1, #904]
	movz w9, #7616, lsl #0
	movk w9, #4, lsl #16
	str w9, [x1, #908]
	movz w9, #50423, lsl #0
	movk w9, #33, lsl #16
	str w9, [x1, #912]
	movz w9, #64501, lsl #0
	movk w9, #112, lsl #16
	str w9, [x1, #916]
	movz w9, #13799, lsl #0
	movk w9, #26, lsl #16
	str w9, [x1, #920]
	movz w9, #13326, lsl #0
	movk w9, #7, lsl #16
	str w9, [x1, #924]
	movz w9, #23878, lsl #0
	movk w9, #121, lsl #16
	str w9, [x1, #928]
	movz w9, #19664, lsl #0
	movk w9, #26, lsl #16
	str w9, [x1, #932]
	movz w9, #23727, lsl #0
	movk w9, #100, lsl #16
	str w9, [x1, #936]
	movz w9, #9832, lsl #0
	movk w9, #29, lsl #16
	str w9, [x1, #940]
	movz w9, #28313, lsl #0
	movk w9, #102, lsl #16
	str w9, [x1, #944]
	movz w9, #1588, lsl #0
	movk w9, #111, lsl #16
	str w9, [x1, #948]
	movz w9, #58843, lsl #0
	movk w9, #123, lsl #16
	str w9, [x1, #952]
	movz w9, #24540, lsl #0
	movk w9, #69, lsl #16
	str w9, [x1, #956]
	movz w9, #1893, lsl #0
	movk w9, #83, lsl #16
	str w9, [x1, #960]
	movz w9, #49584, lsl #0
	movk w9, #93, lsl #16
	str w9, [x1, #964]
	movz w9, #29662, lsl #0
	movk w9, #121, lsl #16
	str w9, [x1, #968]
	movz w9, #64778, lsl #0
	movk w9, #92, lsl #16
	str w9, [x1, #972]
	movz w9, #52371, lsl #0
	movk w9, #2, lsl #16
	str w9, [x1, #976]
	movz w9, #63494, lsl #0
	movk w9, #112, lsl #16
	str w9, [x1, #980]
	movz w9, #39978, lsl #0
	movk w9, #24, lsl #16
	str w9, [x1, #984]
	movz w9, #50602, lsl #0
	movk w9, #73, lsl #16
	str w9, [x1, #988]
	movz w9, #27217, lsl #0
	movk w9, #119, lsl #16
	str w9, [x1, #992]
	movz w9, #53036, lsl #0
	movk w9, #59, lsl #16
	str w9, [x1, #996]
	movz w9, #9039, lsl #0
	movk w9, #127, lsl #16
	str w9, [x1, #1000]
	movz w9, #5856, lsl #0
	movk w9, #107, lsl #16
	str w9, [x1, #1004]
	movz w9, #5578, lsl #0
	movk w9, #60, lsl #16
	str w9, [x1, #1008]
	movz w9, #24168, lsl #0
	movk w9, #21, lsl #16
	str w9, [x1, #1012]
	movz w9, #63159, lsl #0
	movk w9, #114, lsl #16
	str w9, [x1, #1016]
	movz w9, #10702, lsl #0
	movk w9, #30, lsl #16
	str w9, [x1, #1020]
	movz w9, #57345, lsl #0
	movk w9, #127, lsl #16
	movz w10, #57343, lsl #0
	movk w10, #64639, lsl #16
	dup v16.4s, w9
	dup v17.4s, w10
	add x2, x0, #0
	add x3, x1, #4
	movz x4, #1, lsl #0
20:
	ldr w6, [x3, #0]
	add x3, x3, #4
	dup v18.4s, w6
	movz x5, #32, lsl #0
21:
	ldr q0, [x2, #0]
	ldr q1, [x2, #512]
	umull v2.2d, v1.2s, v18.2s
	umull2 v3.2d, v1.4s, v18.4s
	uzp1 v4.4s, v2.4s, v3.4s
	mul v4.4s, v4.4s, v17.4s
	umlal v2.2d, v4.2s, v16.2s
	umlal2 v3.2d, v4.4s, v16.4s
	uzp2 v1.4s, v2.4s, v3.4s
	sub v4.4s, v1.4s, v16.4s
	umin v1.4s, v1.4s, v4.4s
	mov v5.16b, v0.16b
	add v0.4s, v0.4s, v1.4s
	sub v4.4s, v0.4s, v16.4s
	umin v0.4s, v0.4s, v4.4s
	add v5.4s, v5.4s, v16.4s
	sub v5.4s, v5.4s, v1.4s
	sub v4.4s, v5.4s, v16.4s
	umin v5.4s, v5.4s, v4.4s
	str q0, [x2, #0]
	str q5, [x2, #512]
	add x2, x2, #16
	sub x5, x5, #1
	cbnz x5, 21b
	add x2, x2, #512
	sub x4, x4, #1
	cbnz x4, 20b
	add x2, x0, #0
	add x3, x1, #8
	movz x4, #2, lsl #0
22:
	ldr w6, [x3, #0]
	add x3, x3, #4
	dup v18.4s, w6
	movz x5, #16, lsl #0
23:
	ldr q0, [x2, #0]
	ldr q1, [x2, #256]
	umull v2.2d, v1.2s, v18.2s
	umull2 v3.2d, v1.4s, v18.4s
	uzp1 v4.4s, v2.4s, v3.4s
	mul v4.4s, v4.4s, v17.4s
	umlal v2.2d, v4.2s, v16.2s
	umlal2 v3.2d, v4.4s, v16.4s
	uzp2 v1.4s, v2.4s, v3.4s
	sub v4.4s, v1.4s, v16.4s
	umin v1.4s, v1.4s, v4.4s
	mov v5.16b, v0.16b
	add v0.4s, v0.4s, v1.4s
	sub v4.4s, v0.4s, v16.4s
	umin v0.4s, v0.4s, v4.4s
	add v5.4s, v5.4s, v16.4s
	sub v5.4s, v5.4s, v1.4s
	sub v4.4s, v5.4s, v16.4s
	umin v5.4s, v5.4s, v4.4s
	str q0, [x2, #0]
	str q5, [x2, #256]
	add x2, x2, #16
	sub x5, x5, #1
	cbnz x5, 23b
	add x2, x2, #256
	sub x4, x4, #1
	cbnz x4, 22b
	add x2, x0, #0
	add x3, x1, #16
	movz x4, #4, lsl #0
24:
	ldr w6, [x3, #0]
	add x3, x3, #4
	dup v18.4s, w6
	movz x5, #8, lsl #0
25:
	ldr q0, [x2, #0]
	ldr q1, [x2, #128]
	umull v2.2d, v1.2s, v18.2s
	umull2 v3.2d, v1.4s, v18.4s
	uzp1 v4.4s, v2.4s, v3.4s
	mul v4.4s, v4.4s, v17.4s
	umlal v2.2d, v4.2s, v16.2s
	umlal2 v3.2d, v4.4s, v16.4s
	uzp2 v1.4s, v2.4s, v3.4s
	sub v4.4s, v1.4s, v16.4s
	umin v1.4s, v1.4s, v4.4s
	mov v5.16b, v0.16b
	add v0.4s, v0.4s, v1.4s
	sub v4.4s, v0.4s, v16.4s
	umin v0.4s, v0.4s, v4.4s
	add v5.4s, v5.4s, v16.4s
	sub v5.4s, v5.4s, v1.4s
	sub v4.4s, v5.4s, v16.4s
	umin v5.4s, v5.4s, v4.4s
	str q0, [x2, #0]
	str q5, [x2, #128]
	add x2, x2, #16
	sub x5, x5, #1
	cbnz x5, 25b
	add x2, x2, #128
	sub x4, x4, #1
	cbnz x4, 24b
	add x2, x0, #0
	add x3, x1, #32
	movz x4, #8, lsl #0
26:
	ldr w6, [x3, #0]
	add x3, x3, #4
	dup v18.4s, w6
	movz x5, #4, lsl #0
27:
	ldr q0, [x2, #0]
	ldr q1, [x2, #64]
	umull v2.2d, v1.2s, v18.2s
	umull2 v3.2d, v1.4s, v18.4s
	uzp1 v4.4s, v2.4s, v3.4s
	mul v4.4s, v4.4s, v17.4s
	umlal v2.2d, v4.2s, v16.2s
	umlal2 v3.2d, v4.4s, v16.4s
	uzp2 v1.4s, v2.4s, v3.4s
	sub v4.4s, v1.4s, v16.4s
	umin v1.4s, v1.4s, v4.4s
	mov v5.16b, v0.16b
	add v0.4s, v0.4s, v1.4s
	sub v4.4s, v0.4s, v16.4s
	umin v0.4s, v0.4s, v4.4s
	add v5.4s, v5.4s, v16.4s
	sub v5.4s, v5.4s, v1.4s
	sub v4.4s, v5.4s, v16.4s
	umin v5.4s, v5.4s, v4.4s
	str q0, [x2, #0]
	str q5, [x2, #64]
	add x2, x2, #16
	sub x5, x5, #1
	cbnz x5, 27b
	add x2, x2, #64
	sub x4, x4, #1
	cbnz x4, 26b
	add x2, x0, #0
	add x3, x1, #64
	movz x4, #16, lsl #0
28:
	ldr w6, [x3, #0]
	add x3, x3, #4
	dup v18.4s, w6
	movz x5, #2, lsl #0
29:
	ldr q0, [x2, #0]
	ldr q1, [x2, #32]
	umull v2.2d, v1.2s, v18.2s
	umull2 v3.2d, v1.4s, v18.4s
	uzp1 v4.4s, v2.4s, v3.4s
	mul v4.4s, v4.4s, v17.4s
	umlal v2.2d, v4.2s, v16.2s
	umlal2 v3.2d, v4.4s, v16.4s
	uzp2 v1.4s, v2.4s, v3.4s
	sub v4.4s, v1.4s, v16.4s
	umin v1.4s, v1.4s, v4.4s
	mov v5.16b, v0.16b
	add v0.4s, v0.4s, v1.4s
	sub v4.4s, v0.4s, v16.4s
	umin v0.4s, v0.4s, v4.4s
	add v5.4s, v5.4s, v16.4s
	sub v5.4s, v5.4s, v1.4s
	sub v4.4s, v5.4s, v16.4s
	umin v5.4s, v5.4s, v4.4s
	str q0, [x2, #0]
	str q5, [x2, #32]
	add x2, x2, #16
	sub x5, x5, #1
	cbnz x5, 29b
	add x2, x2, #32
	sub x4, x4, #1
	cbnz x4, 28b
	add x2, x0, #0
	add x3, x1, #128
	movz x4, #32, lsl #0
210:
	ldr w6, [x3, #0]
	add x3, x3, #4
	dup v18.4s, w6
	movz x5, #1, lsl #0
211:
	ldr q0, [x2, #0]
	ldr q1, [x2, #16]
	umull v2.2d, v1.2s, v18.2s
	umull2 v3.2d, v1.4s, v18.4s
	uzp1 v4.4s, v2.4s, v3.4s
	mul v4.4s, v4.4s, v17.4s
	umlal v2.2d, v4.2s, v16.2s
	umlal2 v3.2d, v4.4s, v16.4s
	uzp2 v1.4s, v2.4s, v3.4s
	sub v4.4s, v1.4s, v16.4s
	umin v1.4s, v1.4s, v4.4s
	mov v5.16b, v0.16b
	add v0.4s, v0.4s, v1.4s
	sub v4.4s, v0.4s, v16.4s
	umin v0.4s, v0.4s, v4.4s
	add v5.4s, v5.4s, v16.4s
	sub v5.4s, v5.4s, v1.4s
	sub v4.4s, v5.4s, v16.4s
	umin v5.4s, v5.4s, v4.4s
	str q0, [x2, #0]
	str q5, [x2, #16]
	add x2, x2, #16
	sub x5, x5, #1
	cbnz x5, 211b
	add x2, x2, #16
	sub x4, x4, #1
	cbnz x4, 210b
	add x2, x0, #0
	add x3, x1, #256
	movz x5, #32, lsl #0
212:
	ldr q6, [x2, #0]
	ldr q7, [x2, #16]
	ldr q18, [x3, #0]
	zip1 v18.4s, v18.4s, v18.4s
	add x3, x3, #8
	trn1 v0.2d, v6.2d, v7.2d
	trn2 v1.2d, v6.2d, v7.2d
	umull v2.2d, v1.2s, v18.2s
	umull2 v3.2d, v1.4s, v18.4s
	uzp1 v4.4s, v2.4s, v3.4s
	mul v4.4s, v4.4s, v17.4s
	umlal v2.2d, v4.2s, v16.2s
	umlal2 v3.2d, v4.4s, v16.4s
	uzp2 v1.4s, v2.4s, v3.4s
	sub v4.4s, v1.4s, v16.4s
	umin v1.4s, v1.4s, v4.4s
	mov v5.16b, v0.16b
	add v0.4s, v0.4s, v1.4s
	sub v4.4s, v0.4s, v16.4s
	umin v0.4s, v0.4s, v4.4s
	add v5.4s, v5.4s, v16.4s
	sub v5.4s, v5.4s, v1.4s
	sub v4.4s, v5.4s, v16.4s
	umin v5.4s, v5.4s, v4.4s
	trn1 v6.2d, v0.2d, v5.2d
	trn2 v7.2d, v0.2d, v5.2d
	str q6, [x2, #0]
	str q7, [x2, #16]
	add x2, x2, #32
	sub x5, x5, #1
	cbnz x5, 212b
	add x2, x0, #0
	add x3, x1, #512
	movz x5, #32, lsl #0
213:
	ldr q6, [x2, #0]
	ldr q7, [x2, #16]
	ldr q18, [x3, #0]
	add x3, x3, #16
	uzp1 v0.4s, v6.4s, v7.4s
	uzp2 v1.4s, v6.4s, v7.4s
	umull v2.2d, v1.2s, v18.2s
	umull2 v3.2d, v1.4s, v18.4s
	uzp1 v4.4s, v2.4s, v3.4s
	mul v4.4s, v4.4s, v17.4s
	umlal v2.2d, v4.2s, v16.2s
	umlal2 v3.2d, v4.4s, v16.4s
	uzp2 v1.4s, v2.4s, v3.4s
	sub v4.4s, v1.4s, v16.4s
	umin v1.4s, v1.4s, v4.4s
	mov v5.16b, v0.16b
	add v0.4s, v0.4s, v1.4s
	sub v4.4s, v0.4s, v16.4s
	umin v0.4s, v0.4s, v4.4s
	add v5.4s, v5.4s, v16.4s
	sub v5.4s, v5.4s, v1.4s
	sub v4.4s, v5.4s, v16.4s
	umin v5.4s, v5.4s, v4.4s
	zip1 v6.4s, v0.4s, v5.4s
	zip2 v7.4s, v0.4s, v5.4s
	str q6, [x2, #0]
	str q7, [x2, #16]
	add x2, x2, #32
	sub x5, x5, #1
	cbnz x5, 213b
	ret
	.p2align 6
