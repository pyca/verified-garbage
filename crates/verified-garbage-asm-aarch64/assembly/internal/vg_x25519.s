// The functions of `src/internal/vg_x25519.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_x25519:
	str x19, [x3, #0]
	str x20, [x3, #8]
	str x21, [x3, #16]
	str x22, [x3, #24]
	str x23, [x3, #32]
	str x24, [x3, #40]
	movz x20, #1, lsl #0
	ldrb w17, [x1, #0]
	lsr x19, x17, #0
	and x19, x19, x20
	strb w19, [x3, #1984]
	lsr x19, x17, #1
	and x19, x19, x20
	strb w19, [x3, #1985]
	lsr x19, x17, #2
	and x19, x19, x20
	strb w19, [x3, #1986]
	lsr x19, x17, #3
	and x19, x19, x20
	strb w19, [x3, #1987]
	lsr x19, x17, #4
	and x19, x19, x20
	strb w19, [x3, #1988]
	lsr x19, x17, #5
	and x19, x19, x20
	strb w19, [x3, #1989]
	lsr x19, x17, #6
	and x19, x19, x20
	strb w19, [x3, #1990]
	lsr x19, x17, #7
	and x19, x19, x20
	strb w19, [x3, #1991]
	ldrb w17, [x1, #1]
	lsr x19, x17, #0
	and x19, x19, x20
	strb w19, [x3, #1992]
	lsr x19, x17, #1
	and x19, x19, x20
	strb w19, [x3, #1993]
	lsr x19, x17, #2
	and x19, x19, x20
	strb w19, [x3, #1994]
	lsr x19, x17, #3
	and x19, x19, x20
	strb w19, [x3, #1995]
	lsr x19, x17, #4
	and x19, x19, x20
	strb w19, [x3, #1996]
	lsr x19, x17, #5
	and x19, x19, x20
	strb w19, [x3, #1997]
	lsr x19, x17, #6
	and x19, x19, x20
	strb w19, [x3, #1998]
	lsr x19, x17, #7
	and x19, x19, x20
	strb w19, [x3, #1999]
	ldrb w17, [x1, #2]
	lsr x19, x17, #0
	and x19, x19, x20
	strb w19, [x3, #2000]
	lsr x19, x17, #1
	and x19, x19, x20
	strb w19, [x3, #2001]
	lsr x19, x17, #2
	and x19, x19, x20
	strb w19, [x3, #2002]
	lsr x19, x17, #3
	and x19, x19, x20
	strb w19, [x3, #2003]
	lsr x19, x17, #4
	and x19, x19, x20
	strb w19, [x3, #2004]
	lsr x19, x17, #5
	and x19, x19, x20
	strb w19, [x3, #2005]
	lsr x19, x17, #6
	and x19, x19, x20
	strb w19, [x3, #2006]
	lsr x19, x17, #7
	and x19, x19, x20
	strb w19, [x3, #2007]
	ldrb w17, [x1, #3]
	lsr x19, x17, #0
	and x19, x19, x20
	strb w19, [x3, #2008]
	lsr x19, x17, #1
	and x19, x19, x20
	strb w19, [x3, #2009]
	lsr x19, x17, #2
	and x19, x19, x20
	strb w19, [x3, #2010]
	lsr x19, x17, #3
	and x19, x19, x20
	strb w19, [x3, #2011]
	lsr x19, x17, #4
	and x19, x19, x20
	strb w19, [x3, #2012]
	lsr x19, x17, #5
	and x19, x19, x20
	strb w19, [x3, #2013]
	lsr x19, x17, #6
	and x19, x19, x20
	strb w19, [x3, #2014]
	lsr x19, x17, #7
	and x19, x19, x20
	strb w19, [x3, #2015]
	ldrb w17, [x1, #4]
	lsr x19, x17, #0
	and x19, x19, x20
	strb w19, [x3, #2016]
	lsr x19, x17, #1
	and x19, x19, x20
	strb w19, [x3, #2017]
	lsr x19, x17, #2
	and x19, x19, x20
	strb w19, [x3, #2018]
	lsr x19, x17, #3
	and x19, x19, x20
	strb w19, [x3, #2019]
	lsr x19, x17, #4
	and x19, x19, x20
	strb w19, [x3, #2020]
	lsr x19, x17, #5
	and x19, x19, x20
	strb w19, [x3, #2021]
	lsr x19, x17, #6
	and x19, x19, x20
	strb w19, [x3, #2022]
	lsr x19, x17, #7
	and x19, x19, x20
	strb w19, [x3, #2023]
	ldrb w17, [x1, #5]
	lsr x19, x17, #0
	and x19, x19, x20
	strb w19, [x3, #2024]
	lsr x19, x17, #1
	and x19, x19, x20
	strb w19, [x3, #2025]
	lsr x19, x17, #2
	and x19, x19, x20
	strb w19, [x3, #2026]
	lsr x19, x17, #3
	and x19, x19, x20
	strb w19, [x3, #2027]
	lsr x19, x17, #4
	and x19, x19, x20
	strb w19, [x3, #2028]
	lsr x19, x17, #5
	and x19, x19, x20
	strb w19, [x3, #2029]
	lsr x19, x17, #6
	and x19, x19, x20
	strb w19, [x3, #2030]
	lsr x19, x17, #7
	and x19, x19, x20
	strb w19, [x3, #2031]
	ldrb w17, [x1, #6]
	lsr x19, x17, #0
	and x19, x19, x20
	strb w19, [x3, #2032]
	lsr x19, x17, #1
	and x19, x19, x20
	strb w19, [x3, #2033]
	lsr x19, x17, #2
	and x19, x19, x20
	strb w19, [x3, #2034]
	lsr x19, x17, #3
	and x19, x19, x20
	strb w19, [x3, #2035]
	lsr x19, x17, #4
	and x19, x19, x20
	strb w19, [x3, #2036]
	lsr x19, x17, #5
	and x19, x19, x20
	strb w19, [x3, #2037]
	lsr x19, x17, #6
	and x19, x19, x20
	strb w19, [x3, #2038]
	lsr x19, x17, #7
	and x19, x19, x20
	strb w19, [x3, #2039]
	ldrb w17, [x1, #7]
	lsr x19, x17, #0
	and x19, x19, x20
	strb w19, [x3, #2040]
	lsr x19, x17, #1
	and x19, x19, x20
	strb w19, [x3, #2041]
	lsr x19, x17, #2
	and x19, x19, x20
	strb w19, [x3, #2042]
	lsr x19, x17, #3
	and x19, x19, x20
	strb w19, [x3, #2043]
	lsr x19, x17, #4
	and x19, x19, x20
	strb w19, [x3, #2044]
	lsr x19, x17, #5
	and x19, x19, x20
	strb w19, [x3, #2045]
	lsr x19, x17, #6
	and x19, x19, x20
	strb w19, [x3, #2046]
	lsr x19, x17, #7
	and x19, x19, x20
	strb w19, [x3, #2047]
	ldrb w17, [x1, #8]
	lsr x19, x17, #0
	and x19, x19, x20
	strb w19, [x3, #2048]
	lsr x19, x17, #1
	and x19, x19, x20
	strb w19, [x3, #2049]
	lsr x19, x17, #2
	and x19, x19, x20
	strb w19, [x3, #2050]
	lsr x19, x17, #3
	and x19, x19, x20
	strb w19, [x3, #2051]
	lsr x19, x17, #4
	and x19, x19, x20
	strb w19, [x3, #2052]
	lsr x19, x17, #5
	and x19, x19, x20
	strb w19, [x3, #2053]
	lsr x19, x17, #6
	and x19, x19, x20
	strb w19, [x3, #2054]
	lsr x19, x17, #7
	and x19, x19, x20
	strb w19, [x3, #2055]
	ldrb w17, [x1, #9]
	lsr x19, x17, #0
	and x19, x19, x20
	strb w19, [x3, #2056]
	lsr x19, x17, #1
	and x19, x19, x20
	strb w19, [x3, #2057]
	lsr x19, x17, #2
	and x19, x19, x20
	strb w19, [x3, #2058]
	lsr x19, x17, #3
	and x19, x19, x20
	strb w19, [x3, #2059]
	lsr x19, x17, #4
	and x19, x19, x20
	strb w19, [x3, #2060]
	lsr x19, x17, #5
	and x19, x19, x20
	strb w19, [x3, #2061]
	lsr x19, x17, #6
	and x19, x19, x20
	strb w19, [x3, #2062]
	lsr x19, x17, #7
	and x19, x19, x20
	strb w19, [x3, #2063]
	ldrb w17, [x1, #10]
	lsr x19, x17, #0
	and x19, x19, x20
	strb w19, [x3, #2064]
	lsr x19, x17, #1
	and x19, x19, x20
	strb w19, [x3, #2065]
	lsr x19, x17, #2
	and x19, x19, x20
	strb w19, [x3, #2066]
	lsr x19, x17, #3
	and x19, x19, x20
	strb w19, [x3, #2067]
	lsr x19, x17, #4
	and x19, x19, x20
	strb w19, [x3, #2068]
	lsr x19, x17, #5
	and x19, x19, x20
	strb w19, [x3, #2069]
	lsr x19, x17, #6
	and x19, x19, x20
	strb w19, [x3, #2070]
	lsr x19, x17, #7
	and x19, x19, x20
	strb w19, [x3, #2071]
	ldrb w17, [x1, #11]
	lsr x19, x17, #0
	and x19, x19, x20
	strb w19, [x3, #2072]
	lsr x19, x17, #1
	and x19, x19, x20
	strb w19, [x3, #2073]
	lsr x19, x17, #2
	and x19, x19, x20
	strb w19, [x3, #2074]
	lsr x19, x17, #3
	and x19, x19, x20
	strb w19, [x3, #2075]
	lsr x19, x17, #4
	and x19, x19, x20
	strb w19, [x3, #2076]
	lsr x19, x17, #5
	and x19, x19, x20
	strb w19, [x3, #2077]
	lsr x19, x17, #6
	and x19, x19, x20
	strb w19, [x3, #2078]
	lsr x19, x17, #7
	and x19, x19, x20
	strb w19, [x3, #2079]
	ldrb w17, [x1, #12]
	lsr x19, x17, #0
	and x19, x19, x20
	strb w19, [x3, #2080]
	lsr x19, x17, #1
	and x19, x19, x20
	strb w19, [x3, #2081]
	lsr x19, x17, #2
	and x19, x19, x20
	strb w19, [x3, #2082]
	lsr x19, x17, #3
	and x19, x19, x20
	strb w19, [x3, #2083]
	lsr x19, x17, #4
	and x19, x19, x20
	strb w19, [x3, #2084]
	lsr x19, x17, #5
	and x19, x19, x20
	strb w19, [x3, #2085]
	lsr x19, x17, #6
	and x19, x19, x20
	strb w19, [x3, #2086]
	lsr x19, x17, #7
	and x19, x19, x20
	strb w19, [x3, #2087]
	ldrb w17, [x1, #13]
	lsr x19, x17, #0
	and x19, x19, x20
	strb w19, [x3, #2088]
	lsr x19, x17, #1
	and x19, x19, x20
	strb w19, [x3, #2089]
	lsr x19, x17, #2
	and x19, x19, x20
	strb w19, [x3, #2090]
	lsr x19, x17, #3
	and x19, x19, x20
	strb w19, [x3, #2091]
	lsr x19, x17, #4
	and x19, x19, x20
	strb w19, [x3, #2092]
	lsr x19, x17, #5
	and x19, x19, x20
	strb w19, [x3, #2093]
	lsr x19, x17, #6
	and x19, x19, x20
	strb w19, [x3, #2094]
	lsr x19, x17, #7
	and x19, x19, x20
	strb w19, [x3, #2095]
	ldrb w17, [x1, #14]
	lsr x19, x17, #0
	and x19, x19, x20
	strb w19, [x3, #2096]
	lsr x19, x17, #1
	and x19, x19, x20
	strb w19, [x3, #2097]
	lsr x19, x17, #2
	and x19, x19, x20
	strb w19, [x3, #2098]
	lsr x19, x17, #3
	and x19, x19, x20
	strb w19, [x3, #2099]
	lsr x19, x17, #4
	and x19, x19, x20
	strb w19, [x3, #2100]
	lsr x19, x17, #5
	and x19, x19, x20
	strb w19, [x3, #2101]
	lsr x19, x17, #6
	and x19, x19, x20
	strb w19, [x3, #2102]
	lsr x19, x17, #7
	and x19, x19, x20
	strb w19, [x3, #2103]
	ldrb w17, [x1, #15]
	lsr x19, x17, #0
	and x19, x19, x20
	strb w19, [x3, #2104]
	lsr x19, x17, #1
	and x19, x19, x20
	strb w19, [x3, #2105]
	lsr x19, x17, #2
	and x19, x19, x20
	strb w19, [x3, #2106]
	lsr x19, x17, #3
	and x19, x19, x20
	strb w19, [x3, #2107]
	lsr x19, x17, #4
	and x19, x19, x20
	strb w19, [x3, #2108]
	lsr x19, x17, #5
	and x19, x19, x20
	strb w19, [x3, #2109]
	lsr x19, x17, #6
	and x19, x19, x20
	strb w19, [x3, #2110]
	lsr x19, x17, #7
	and x19, x19, x20
	strb w19, [x3, #2111]
	ldrb w17, [x1, #16]
	lsr x19, x17, #0
	and x19, x19, x20
	strb w19, [x3, #2112]
	lsr x19, x17, #1
	and x19, x19, x20
	strb w19, [x3, #2113]
	lsr x19, x17, #2
	and x19, x19, x20
	strb w19, [x3, #2114]
	lsr x19, x17, #3
	and x19, x19, x20
	strb w19, [x3, #2115]
	lsr x19, x17, #4
	and x19, x19, x20
	strb w19, [x3, #2116]
	lsr x19, x17, #5
	and x19, x19, x20
	strb w19, [x3, #2117]
	lsr x19, x17, #6
	and x19, x19, x20
	strb w19, [x3, #2118]
	lsr x19, x17, #7
	and x19, x19, x20
	strb w19, [x3, #2119]
	ldrb w17, [x1, #17]
	lsr x19, x17, #0
	and x19, x19, x20
	strb w19, [x3, #2120]
	lsr x19, x17, #1
	and x19, x19, x20
	strb w19, [x3, #2121]
	lsr x19, x17, #2
	and x19, x19, x20
	strb w19, [x3, #2122]
	lsr x19, x17, #3
	and x19, x19, x20
	strb w19, [x3, #2123]
	lsr x19, x17, #4
	and x19, x19, x20
	strb w19, [x3, #2124]
	lsr x19, x17, #5
	and x19, x19, x20
	strb w19, [x3, #2125]
	lsr x19, x17, #6
	and x19, x19, x20
	strb w19, [x3, #2126]
	lsr x19, x17, #7
	and x19, x19, x20
	strb w19, [x3, #2127]
	ldrb w17, [x1, #18]
	lsr x19, x17, #0
	and x19, x19, x20
	strb w19, [x3, #2128]
	lsr x19, x17, #1
	and x19, x19, x20
	strb w19, [x3, #2129]
	lsr x19, x17, #2
	and x19, x19, x20
	strb w19, [x3, #2130]
	lsr x19, x17, #3
	and x19, x19, x20
	strb w19, [x3, #2131]
	lsr x19, x17, #4
	and x19, x19, x20
	strb w19, [x3, #2132]
	lsr x19, x17, #5
	and x19, x19, x20
	strb w19, [x3, #2133]
	lsr x19, x17, #6
	and x19, x19, x20
	strb w19, [x3, #2134]
	lsr x19, x17, #7
	and x19, x19, x20
	strb w19, [x3, #2135]
	ldrb w17, [x1, #19]
	lsr x19, x17, #0
	and x19, x19, x20
	strb w19, [x3, #2136]
	lsr x19, x17, #1
	and x19, x19, x20
	strb w19, [x3, #2137]
	lsr x19, x17, #2
	and x19, x19, x20
	strb w19, [x3, #2138]
	lsr x19, x17, #3
	and x19, x19, x20
	strb w19, [x3, #2139]
	lsr x19, x17, #4
	and x19, x19, x20
	strb w19, [x3, #2140]
	lsr x19, x17, #5
	and x19, x19, x20
	strb w19, [x3, #2141]
	lsr x19, x17, #6
	and x19, x19, x20
	strb w19, [x3, #2142]
	lsr x19, x17, #7
	and x19, x19, x20
	strb w19, [x3, #2143]
	ldrb w17, [x1, #20]
	lsr x19, x17, #0
	and x19, x19, x20
	strb w19, [x3, #2144]
	lsr x19, x17, #1
	and x19, x19, x20
	strb w19, [x3, #2145]
	lsr x19, x17, #2
	and x19, x19, x20
	strb w19, [x3, #2146]
	lsr x19, x17, #3
	and x19, x19, x20
	strb w19, [x3, #2147]
	lsr x19, x17, #4
	and x19, x19, x20
	strb w19, [x3, #2148]
	lsr x19, x17, #5
	and x19, x19, x20
	strb w19, [x3, #2149]
	lsr x19, x17, #6
	and x19, x19, x20
	strb w19, [x3, #2150]
	lsr x19, x17, #7
	and x19, x19, x20
	strb w19, [x3, #2151]
	ldrb w17, [x1, #21]
	lsr x19, x17, #0
	and x19, x19, x20
	strb w19, [x3, #2152]
	lsr x19, x17, #1
	and x19, x19, x20
	strb w19, [x3, #2153]
	lsr x19, x17, #2
	and x19, x19, x20
	strb w19, [x3, #2154]
	lsr x19, x17, #3
	and x19, x19, x20
	strb w19, [x3, #2155]
	lsr x19, x17, #4
	and x19, x19, x20
	strb w19, [x3, #2156]
	lsr x19, x17, #5
	and x19, x19, x20
	strb w19, [x3, #2157]
	lsr x19, x17, #6
	and x19, x19, x20
	strb w19, [x3, #2158]
	lsr x19, x17, #7
	and x19, x19, x20
	strb w19, [x3, #2159]
	ldrb w17, [x1, #22]
	lsr x19, x17, #0
	and x19, x19, x20
	strb w19, [x3, #2160]
	lsr x19, x17, #1
	and x19, x19, x20
	strb w19, [x3, #2161]
	lsr x19, x17, #2
	and x19, x19, x20
	strb w19, [x3, #2162]
	lsr x19, x17, #3
	and x19, x19, x20
	strb w19, [x3, #2163]
	lsr x19, x17, #4
	and x19, x19, x20
	strb w19, [x3, #2164]
	lsr x19, x17, #5
	and x19, x19, x20
	strb w19, [x3, #2165]
	lsr x19, x17, #6
	and x19, x19, x20
	strb w19, [x3, #2166]
	lsr x19, x17, #7
	and x19, x19, x20
	strb w19, [x3, #2167]
	ldrb w17, [x1, #23]
	lsr x19, x17, #0
	and x19, x19, x20
	strb w19, [x3, #2168]
	lsr x19, x17, #1
	and x19, x19, x20
	strb w19, [x3, #2169]
	lsr x19, x17, #2
	and x19, x19, x20
	strb w19, [x3, #2170]
	lsr x19, x17, #3
	and x19, x19, x20
	strb w19, [x3, #2171]
	lsr x19, x17, #4
	and x19, x19, x20
	strb w19, [x3, #2172]
	lsr x19, x17, #5
	and x19, x19, x20
	strb w19, [x3, #2173]
	lsr x19, x17, #6
	and x19, x19, x20
	strb w19, [x3, #2174]
	lsr x19, x17, #7
	and x19, x19, x20
	strb w19, [x3, #2175]
	ldrb w17, [x1, #24]
	lsr x19, x17, #0
	and x19, x19, x20
	strb w19, [x3, #2176]
	lsr x19, x17, #1
	and x19, x19, x20
	strb w19, [x3, #2177]
	lsr x19, x17, #2
	and x19, x19, x20
	strb w19, [x3, #2178]
	lsr x19, x17, #3
	and x19, x19, x20
	strb w19, [x3, #2179]
	lsr x19, x17, #4
	and x19, x19, x20
	strb w19, [x3, #2180]
	lsr x19, x17, #5
	and x19, x19, x20
	strb w19, [x3, #2181]
	lsr x19, x17, #6
	and x19, x19, x20
	strb w19, [x3, #2182]
	lsr x19, x17, #7
	and x19, x19, x20
	strb w19, [x3, #2183]
	ldrb w17, [x1, #25]
	lsr x19, x17, #0
	and x19, x19, x20
	strb w19, [x3, #2184]
	lsr x19, x17, #1
	and x19, x19, x20
	strb w19, [x3, #2185]
	lsr x19, x17, #2
	and x19, x19, x20
	strb w19, [x3, #2186]
	lsr x19, x17, #3
	and x19, x19, x20
	strb w19, [x3, #2187]
	lsr x19, x17, #4
	and x19, x19, x20
	strb w19, [x3, #2188]
	lsr x19, x17, #5
	and x19, x19, x20
	strb w19, [x3, #2189]
	lsr x19, x17, #6
	and x19, x19, x20
	strb w19, [x3, #2190]
	lsr x19, x17, #7
	and x19, x19, x20
	strb w19, [x3, #2191]
	ldrb w17, [x1, #26]
	lsr x19, x17, #0
	and x19, x19, x20
	strb w19, [x3, #2192]
	lsr x19, x17, #1
	and x19, x19, x20
	strb w19, [x3, #2193]
	lsr x19, x17, #2
	and x19, x19, x20
	strb w19, [x3, #2194]
	lsr x19, x17, #3
	and x19, x19, x20
	strb w19, [x3, #2195]
	lsr x19, x17, #4
	and x19, x19, x20
	strb w19, [x3, #2196]
	lsr x19, x17, #5
	and x19, x19, x20
	strb w19, [x3, #2197]
	lsr x19, x17, #6
	and x19, x19, x20
	strb w19, [x3, #2198]
	lsr x19, x17, #7
	and x19, x19, x20
	strb w19, [x3, #2199]
	ldrb w17, [x1, #27]
	lsr x19, x17, #0
	and x19, x19, x20
	strb w19, [x3, #2200]
	lsr x19, x17, #1
	and x19, x19, x20
	strb w19, [x3, #2201]
	lsr x19, x17, #2
	and x19, x19, x20
	strb w19, [x3, #2202]
	lsr x19, x17, #3
	and x19, x19, x20
	strb w19, [x3, #2203]
	lsr x19, x17, #4
	and x19, x19, x20
	strb w19, [x3, #2204]
	lsr x19, x17, #5
	and x19, x19, x20
	strb w19, [x3, #2205]
	lsr x19, x17, #6
	and x19, x19, x20
	strb w19, [x3, #2206]
	lsr x19, x17, #7
	and x19, x19, x20
	strb w19, [x3, #2207]
	ldrb w17, [x1, #28]
	lsr x19, x17, #0
	and x19, x19, x20
	strb w19, [x3, #2208]
	lsr x19, x17, #1
	and x19, x19, x20
	strb w19, [x3, #2209]
	lsr x19, x17, #2
	and x19, x19, x20
	strb w19, [x3, #2210]
	lsr x19, x17, #3
	and x19, x19, x20
	strb w19, [x3, #2211]
	lsr x19, x17, #4
	and x19, x19, x20
	strb w19, [x3, #2212]
	lsr x19, x17, #5
	and x19, x19, x20
	strb w19, [x3, #2213]
	lsr x19, x17, #6
	and x19, x19, x20
	strb w19, [x3, #2214]
	lsr x19, x17, #7
	and x19, x19, x20
	strb w19, [x3, #2215]
	ldrb w17, [x1, #29]
	lsr x19, x17, #0
	and x19, x19, x20
	strb w19, [x3, #2216]
	lsr x19, x17, #1
	and x19, x19, x20
	strb w19, [x3, #2217]
	lsr x19, x17, #2
	and x19, x19, x20
	strb w19, [x3, #2218]
	lsr x19, x17, #3
	and x19, x19, x20
	strb w19, [x3, #2219]
	lsr x19, x17, #4
	and x19, x19, x20
	strb w19, [x3, #2220]
	lsr x19, x17, #5
	and x19, x19, x20
	strb w19, [x3, #2221]
	lsr x19, x17, #6
	and x19, x19, x20
	strb w19, [x3, #2222]
	lsr x19, x17, #7
	and x19, x19, x20
	strb w19, [x3, #2223]
	ldrb w17, [x1, #30]
	lsr x19, x17, #0
	and x19, x19, x20
	strb w19, [x3, #2224]
	lsr x19, x17, #1
	and x19, x19, x20
	strb w19, [x3, #2225]
	lsr x19, x17, #2
	and x19, x19, x20
	strb w19, [x3, #2226]
	lsr x19, x17, #3
	and x19, x19, x20
	strb w19, [x3, #2227]
	lsr x19, x17, #4
	and x19, x19, x20
	strb w19, [x3, #2228]
	lsr x19, x17, #5
	and x19, x19, x20
	strb w19, [x3, #2229]
	lsr x19, x17, #6
	and x19, x19, x20
	strb w19, [x3, #2230]
	lsr x19, x17, #7
	and x19, x19, x20
	strb w19, [x3, #2231]
	ldrb w17, [x1, #31]
	lsr x19, x17, #0
	and x19, x19, x20
	strb w19, [x3, #2232]
	lsr x19, x17, #1
	and x19, x19, x20
	strb w19, [x3, #2233]
	lsr x19, x17, #2
	and x19, x19, x20
	strb w19, [x3, #2234]
	lsr x19, x17, #3
	and x19, x19, x20
	strb w19, [x3, #2235]
	lsr x19, x17, #4
	and x19, x19, x20
	strb w19, [x3, #2236]
	lsr x19, x17, #5
	and x19, x19, x20
	strb w19, [x3, #2237]
	lsr x19, x17, #6
	and x19, x19, x20
	strb w19, [x3, #2238]
	lsr x19, x17, #7
	and x19, x19, x20
	strb w19, [x3, #2239]
	movz x19, #0, lsl #0
	strb w19, [x3, #1984]
	strb w19, [x3, #1985]
	strb w19, [x3, #1986]
	strb w20, [x3, #2238]
	movz x19, #0, lsl #0
	strb w19, [x3, #2239]
	add x1, x0, #0
	add x0, x3, #0
	ldr x4, [x2, #0]
	ldr x5, [x2, #8]
	ldr x6, [x2, #16]
	ldr x7, [x2, #24]
	movz x8, #65535, lsl #0
	movk x8, #65535, lsl #16
	movk x8, #65535, lsl #32
	movk x8, #32767, lsl #48
	and x7, x7, x8
	str x4, [x0, #64]
	str x5, [x0, #72]
	str x6, [x0, #80]
	str x7, [x0, #88]
	ldr x4, [x0, #64]
	ldr x5, [x0, #72]
	ldr x6, [x0, #80]
	ldr x7, [x0, #88]
	str x4, [x0, #160]
	str x5, [x0, #168]
	str x6, [x0, #176]
	str x7, [x0, #184]
	movz x4, #1, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	movz x5, #0, lsl #0
	movk x5, #0, lsl #16
	movk x5, #0, lsl #32
	movk x5, #0, lsl #48
	movz x6, #0, lsl #0
	movk x6, #0, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	movz x7, #0, lsl #0
	movk x7, #0, lsl #16
	movk x7, #0, lsl #32
	movk x7, #0, lsl #48
	str x4, [x0, #96]
	str x5, [x0, #104]
	str x6, [x0, #112]
	str x7, [x0, #120]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	movz x5, #0, lsl #0
	movk x5, #0, lsl #16
	movk x5, #0, lsl #32
	movk x5, #0, lsl #48
	movz x6, #0, lsl #0
	movk x6, #0, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	movz x7, #0, lsl #0
	movk x7, #0, lsl #16
	movk x7, #0, lsl #32
	movk x7, #0, lsl #48
	str x4, [x0, #128]
	str x5, [x0, #136]
	str x6, [x0, #144]
	str x7, [x0, #152]
	movz x4, #1, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	movz x5, #0, lsl #0
	movk x5, #0, lsl #16
	movk x5, #0, lsl #32
	movk x5, #0, lsl #48
	movz x6, #0, lsl #0
	movk x6, #0, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	movz x7, #0, lsl #0
	movk x7, #0, lsl #16
	movk x7, #0, lsl #32
	movk x7, #0, lsl #48
	str x4, [x0, #192]
	str x5, [x0, #200]
	str x6, [x0, #208]
	str x7, [x0, #216]
	movz w10, #0, lsl #0
	movz w19, #255, lsl #0
20:
	ldp x4, x5, [x0, #96]
	ldp x6, x7, [x0, #112]
	ldp x12, x13, [x0, #160]
	ldp x14, x15, [x0, #176]
	ldp x21, x22, [x0, #128]
	ldp x23, x24, [x0, #144]
	ldp x2, x3, [x0, #192]
	ldp x8, x9, [x0, #208]
	sub x19, x19, #1
	add x17, x0, x19
	ldrb w16, [x17, #1984]
	ldrb w17, [x17, #1985]
	eor x16, x16, x17
	tst x16, x16
	csel x11, x12, x4, ne
	csel x12, x4, x12, ne
	csel x4, x13, x5, ne
	csel x13, x5, x13, ne
	csel x5, x14, x6, ne
	csel x14, x6, x14, ne
	csel x6, x15, x7, ne
	csel x15, x7, x15, ne
	csel x7, x2, x21, ne
	csel x2, x21, x2, ne
	csel x21, x3, x22, ne
	csel x3, x22, x3, ne
	csel x22, x8, x23, ne
	csel x8, x23, x8, ne
	csel x23, x9, x24, ne
	csel x9, x24, x9, ne
	stp x2, x3, [x0, #192]
	stp x8, x9, [x0, #208]
	adds x16, x11, x7
	adcs x17, x4, x21
	movz w2, #38, lsl #0
	adcs x20, x5, x22
	adcs x24, x6, x23
	csel x3, x2, x10, hs
	adds x16, x16, x3
	adcs x17, x17, x10
	adc x20, x20, x10
	stp x16, x17, [x0, #224]
	stp x20, x24, [x0, #240]
	subs x11, x11, x7
	sbcs x4, x4, x21
	movz w2, #38, lsl #0
	sbcs x5, x5, x22
	sbcs x6, x6, x23
	csel x3, x10, x2, hs
	subs x11, x11, x3
	sbcs x4, x4, x10
	sbcs x5, x5, x10
	sbc x6, x6, x10
	stp x11, x4, [x0, #256]
	stp x5, x6, [x0, #272]
	ldp x21, x22, [x0, #192]
	ldp x23, x24, [x0, #208]
	adds x4, x12, x21
	adcs x5, x13, x22
	movz w2, #38, lsl #0
	adcs x6, x14, x23
	adcs x7, x15, x24
	csel x3, x2, x10, hs
	adds x4, x4, x3
	adcs x5, x5, x10
	adc x6, x6, x10
	stp x4, x5, [x0, #288]
	stp x6, x7, [x0, #304]
	subs x12, x12, x21
	sbcs x13, x13, x22
	movz w2, #38, lsl #0
	sbcs x14, x14, x23
	sbcs x15, x15, x24
	csel x3, x10, x2, hs
	subs x12, x12, x3
	sbcs x13, x13, x10
	sbcs x14, x14, x10
	sbc x15, x15, x10
	stp x12, x13, [x0, #320]
	stp x14, x15, [x0, #336]
	ldp x12, x13, [x0, #224]
	ldp x14, x15, [x0, #240]
	mul x5, x12, x13
	mul x6, x12, x14
	mul x7, x12, x15
	umulh x2, x12, x13
	umulh x8, x12, x14
	umulh x9, x12, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adc x21, x9, x10
	mul x2, x13, x14
	mul x8, x13, x15
	umulh x9, x13, x14
	umulh x16, x13, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adc x22, x16, x10
	adds x21, x21, x9
	adc x22, x22, x10
	mul x2, x14, x15
	umulh x8, x14, x15
	adds x22, x22, x2
	adc x23, x8, x10
	adds x5, x5, x5
	adcs x6, x6, x6
	adcs x7, x7, x7
	adcs x21, x21, x21
	adcs x22, x22, x22
	adcs x23, x23, x23
	adc x24, x10, x10
	mul x4, x12, x12
	umulh x2, x12, x12
	mul x8, x13, x13
	umulh x9, x13, x13
	mul x16, x14, x14
	umulh x17, x14, x14
	mul x3, x15, x15
	umulh x11, x15, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adcs x22, x22, x17
	adcs x23, x23, x3
	adc x24, x24, x11
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adc x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adc x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adc x7, x7, x10
	stp x4, x5, [x0, #352]
	stp x6, x7, [x0, #368]
	ldp x12, x13, [x0, #256]
	ldp x14, x15, [x0, #272]
	mul x5, x12, x13
	mul x6, x12, x14
	mul x7, x12, x15
	umulh x2, x12, x13
	umulh x8, x12, x14
	umulh x9, x12, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adc x21, x9, x10
	mul x2, x13, x14
	mul x8, x13, x15
	umulh x9, x13, x14
	umulh x16, x13, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adc x22, x16, x10
	adds x21, x21, x9
	adc x22, x22, x10
	mul x2, x14, x15
	umulh x8, x14, x15
	adds x22, x22, x2
	adc x23, x8, x10
	adds x5, x5, x5
	adcs x6, x6, x6
	adcs x7, x7, x7
	adcs x21, x21, x21
	adcs x22, x22, x22
	adcs x23, x23, x23
	adc x24, x10, x10
	mul x4, x12, x12
	umulh x2, x12, x12
	mul x8, x13, x13
	umulh x9, x13, x13
	mul x16, x14, x14
	umulh x17, x14, x14
	mul x3, x15, x15
	umulh x11, x15, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adcs x22, x22, x17
	adcs x23, x23, x3
	adc x24, x24, x11
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adc x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adc x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adc x7, x7, x10
	stp x4, x5, [x0, #384]
	stp x6, x7, [x0, #400]
	ldp x12, x13, [x0, #224]
	ldp x14, x15, [x0, #240]
	ldr x3, [x0, #320]
	mul x4, x3, x12
	mul x5, x3, x13
	mul x6, x3, x14
	mul x7, x3, x15
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adc x21, x16, x10
	ldr x3, [x0, #328]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adc x22, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adc x22, x22, x16
	ldr x3, [x0, #336]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	adc x23, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adc x23, x23, x16
	ldr x3, [x0, #344]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	adc x24, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x21, x21, x2
	adcs x22, x22, x8
	adcs x23, x23, x9
	adc x24, x24, x16
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adc x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adc x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adc x7, x7, x10
	stp x4, x5, [x0, #448]
	stp x6, x7, [x0, #464]
	ldp x12, x13, [x0, #256]
	ldp x14, x15, [x0, #272]
	ldr x3, [x0, #288]
	mul x4, x3, x12
	mul x5, x3, x13
	mul x6, x3, x14
	mul x7, x3, x15
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adc x21, x16, x10
	ldr x3, [x0, #296]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adc x22, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adc x22, x22, x16
	ldr x3, [x0, #304]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	adc x23, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adc x23, x23, x16
	ldr x3, [x0, #312]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	adc x24, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x21, x21, x2
	adcs x22, x22, x8
	adcs x23, x23, x9
	adc x24, x24, x16
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adc x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adc x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adc x7, x7, x10
	stp x4, x5, [x0, #480]
	stp x6, x7, [x0, #496]
	ldp x4, x5, [x0, #352]
	ldp x6, x7, [x0, #368]
	ldp x21, x22, [x0, #384]
	ldp x23, x24, [x0, #400]
	subs x12, x4, x21
	sbcs x13, x5, x22
	movz w2, #38, lsl #0
	sbcs x14, x6, x23
	sbcs x15, x7, x24
	csel x3, x10, x2, hs
	subs x12, x12, x3
	sbcs x13, x13, x10
	sbcs x14, x14, x10
	sbc x15, x15, x10
	stp x12, x13, [x0, #416]
	stp x14, x15, [x0, #432]
	ldp x12, x13, [x0, #384]
	ldp x14, x15, [x0, #400]
	ldr x3, [x0, #352]
	mul x4, x3, x12
	mul x5, x3, x13
	mul x6, x3, x14
	mul x7, x3, x15
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adc x21, x16, x10
	ldr x3, [x0, #360]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adc x22, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adc x22, x22, x16
	ldr x3, [x0, #368]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	adc x23, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adc x23, x23, x16
	ldr x3, [x0, #376]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	adc x24, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x21, x21, x2
	adcs x22, x22, x8
	adcs x23, x23, x9
	adc x24, x24, x16
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adc x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adc x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adc x7, x7, x10
	stp x4, x5, [x0, #96]
	stp x6, x7, [x0, #112]
	ldp x4, x5, [x0, #352]
	ldp x6, x7, [x0, #368]
	ldp x12, x13, [x0, #416]
	ldp x14, x15, [x0, #432]
	movz x11, #56129, lsl #0
	movk x11, #1, lsl #16
	mul x2, x12, x11
	mul x3, x13, x11
	mul x8, x14, x11
	mul x9, x15, x11
	umulh x20, x15, x11
	adds x4, x4, x2
	adcs x5, x5, x3
	adcs x6, x6, x8
	adcs x7, x7, x9
	adc x20, x20, x10
	umulh x2, x12, x11
	umulh x3, x13, x11
	umulh x8, x14, x11
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x12, x4, x9
	adcs x13, x5, x2
	adcs x14, x6, x3
	adc x15, x7, x8
	ldr x3, [x0, #416]
	mul x4, x3, x12
	mul x5, x3, x13
	mul x6, x3, x14
	mul x7, x3, x15
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adc x21, x16, x10
	ldr x3, [x0, #424]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adc x22, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adc x22, x22, x16
	ldr x3, [x0, #432]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	adc x23, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adc x23, x23, x16
	ldr x3, [x0, #440]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	adc x24, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x21, x21, x2
	adcs x22, x22, x8
	adcs x23, x23, x9
	adc x24, x24, x16
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adc x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adc x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adc x7, x7, x10
	stp x4, x5, [x0, #128]
	stp x6, x7, [x0, #144]
	ldp x4, x5, [x0, #448]
	ldp x6, x7, [x0, #464]
	ldp x21, x22, [x0, #480]
	ldp x23, x24, [x0, #496]
	subs x12, x4, x21
	sbcs x13, x5, x22
	movz w2, #38, lsl #0
	sbcs x14, x6, x23
	sbcs x15, x7, x24
	csel x3, x10, x2, hs
	subs x12, x12, x3
	sbcs x13, x13, x10
	sbcs x14, x14, x10
	sbc x15, x15, x10
	mul x5, x12, x13
	mul x6, x12, x14
	mul x7, x12, x15
	umulh x2, x12, x13
	umulh x8, x12, x14
	umulh x9, x12, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adc x21, x9, x10
	mul x2, x13, x14
	mul x8, x13, x15
	umulh x9, x13, x14
	umulh x16, x13, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adc x22, x16, x10
	adds x21, x21, x9
	adc x22, x22, x10
	mul x2, x14, x15
	umulh x8, x14, x15
	adds x22, x22, x2
	adc x23, x8, x10
	adds x5, x5, x5
	adcs x6, x6, x6
	adcs x7, x7, x7
	adcs x21, x21, x21
	adcs x22, x22, x22
	adcs x23, x23, x23
	adc x24, x10, x10
	mul x4, x12, x12
	umulh x2, x12, x12
	mul x8, x13, x13
	umulh x9, x13, x13
	mul x16, x14, x14
	umulh x17, x14, x14
	mul x3, x15, x15
	umulh x11, x15, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adcs x22, x22, x17
	adcs x23, x23, x3
	adc x24, x24, x11
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adc x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adc x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adc x7, x7, x10
	stp x4, x5, [x0, #192]
	stp x6, x7, [x0, #208]
	ldp x4, x5, [x0, #448]
	ldp x6, x7, [x0, #464]
	ldp x21, x22, [x0, #480]
	ldp x23, x24, [x0, #496]
	adds x12, x4, x21
	adcs x13, x5, x22
	movz w2, #38, lsl #0
	adcs x14, x6, x23
	adcs x15, x7, x24
	csel x3, x2, x10, hs
	adds x12, x12, x3
	adcs x13, x13, x10
	adc x14, x14, x10
	mul x5, x12, x13
	mul x6, x12, x14
	mul x7, x12, x15
	umulh x2, x12, x13
	umulh x8, x12, x14
	umulh x9, x12, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adc x21, x9, x10
	mul x2, x13, x14
	mul x8, x13, x15
	umulh x9, x13, x14
	umulh x16, x13, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adc x22, x16, x10
	adds x21, x21, x9
	adc x22, x22, x10
	mul x2, x14, x15
	umulh x8, x14, x15
	adds x22, x22, x2
	adc x23, x8, x10
	adds x5, x5, x5
	adcs x6, x6, x6
	adcs x7, x7, x7
	adcs x21, x21, x21
	adcs x22, x22, x22
	adcs x23, x23, x23
	adc x24, x10, x10
	mul x4, x12, x12
	umulh x2, x12, x12
	mul x8, x13, x13
	umulh x9, x13, x13
	mul x16, x14, x14
	umulh x17, x14, x14
	mul x3, x15, x15
	umulh x11, x15, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adcs x22, x22, x17
	adcs x23, x23, x3
	adc x24, x24, x11
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adc x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adc x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adc x7, x7, x10
	stp x4, x5, [x0, #160]
	stp x6, x7, [x0, #176]
	ldp x12, x13, [x0, #192]
	ldp x14, x15, [x0, #208]
	ldr x3, [x0, #64]
	mul x4, x3, x12
	mul x5, x3, x13
	mul x6, x3, x14
	mul x7, x3, x15
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adc x21, x16, x10
	ldr x3, [x0, #72]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adc x22, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adc x22, x22, x16
	ldr x3, [x0, #80]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	adc x23, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adc x23, x23, x16
	ldr x3, [x0, #88]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	adc x24, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x21, x21, x2
	adcs x22, x22, x8
	adcs x23, x23, x9
	adc x24, x24, x16
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adc x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adc x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adc x7, x7, x10
	stp x4, x5, [x0, #192]
	stp x6, x7, [x0, #208]
	cbnz x19, 20b
	add x19, x1, #0
	movz x12, #0, lsl #0
	movz x6, #19, lsl #0
	movz x7, #65535, lsl #0
	movk x7, #65535, lsl #16
	movk x7, #65535, lsl #32
	movk x7, #32767, lsl #48
	ldr x2, [x0, #128]
	ldr x3, [x0, #136]
	ldr x4, [x0, #144]
	ldr x5, [x0, #152]
	lsr x8, x5, #63
	and x5, x5, x7
	mul x8, x8, x6
	adds x2, x2, x8
	adcs x3, x3, x12
	adcs x4, x4, x12
	adc x5, x5, x12
	adds x8, x2, x6
	adcs x9, x3, x12
	adcs x10, x4, x12
	adc x11, x5, x12
	lsr x13, x11, #63
	and x11, x11, x7
	sub x13, x12, x13
	eor x8, x8, x2
	and x8, x8, x13
	eor x2, x2, x8
	eor x9, x9, x3
	and x9, x9, x13
	eor x3, x3, x9
	eor x10, x10, x4
	and x10, x10, x13
	eor x4, x4, x10
	eor x11, x11, x5
	and x11, x11, x13
	eor x5, x5, x11
	str x2, [x0, #224]
	str x3, [x0, #232]
	str x4, [x0, #240]
	str x5, [x0, #248]
	movz x2, #65517, lsl #0
	movk x2, #65535, lsl #16
	movk x2, #65535, lsl #32
	movk x2, #65535, lsl #48
	str x2, [x0, #192]
	movz x2, #65535, lsl #0
	movk x2, #65535, lsl #16
	movk x2, #65535, lsl #32
	movk x2, #65535, lsl #48
	str x2, [x0, #200]
	movz x2, #65535, lsl #0
	movk x2, #65535, lsl #16
	movk x2, #65535, lsl #32
	movk x2, #65535, lsl #48
	str x2, [x0, #208]
	movz x2, #65535, lsl #0
	movk x2, #65535, lsl #16
	movk x2, #65535, lsl #32
	movk x2, #32767, lsl #48
	str x2, [x0, #216]
	str x12, [x0, #256]
	str x12, [x0, #264]
	str x12, [x0, #272]
	str x12, [x0, #280]
	movz x2, #8345, lsl #0
	movk x2, #29954, lsl #16
	movk x2, #40483, lsl #32
	movk x2, #41209, lsl #48
	str x2, [x0, #288]
	movz x2, #9621, lsl #0
	movk x2, #7443, lsl #16
	movk x2, #36671, lsl #32
	movk x2, #43206, lsl #48
	str x2, [x0, #296]
	movz x2, #21058, lsl #0
	movk x2, #1452, lsl #16
	movk x2, #35128, lsl #32
	movk x2, #27756, lsl #48
	str x2, [x0, #304]
	movz x2, #1557, lsl #0
	movk x2, #16759, lsl #16
	movk x2, #2226, lsl #32
	movk x2, #10085, lsl #48
	str x2, [x0, #312]
	movz x1, #1, lsl #0
	str x1, [x0, #480]
	movz x20, #10, lsl #0
21:
	ldr x1, [x0, #480]
	ldr x2, [x0, #192]
	ldr x3, [x0, #224]
	movz x13, #0, lsl #0
	sub x1, x13, x1
	sub x1, x1, #1
	movz x13, #32767, lsl #0
	and x8, x2, x13
	and x9, x3, x13
	movz x16, #32768, lsl #16
	add x8, x8, x16
	movz x16, #32768, lsl #32
	add x9, x9, x16
	movz x12, #1, lsl #0
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	movz x13, #16384, lsl #16
	movk x13, #8192, lsl #32
	movk x13, #8192, lsl #48
	movz x17, #16384, lsl #0
	add x8, x8, x13
	add x10, x10, x13
	lsr x11, x8, #47
	sub x11, x11, x17
	lsl x8, x8, #17
	lsr x8, x8, #48
	sub x8, x8, x17
	lsr x9, x10, #47
	sub x9, x9, x17
	lsl x10, x10, #17
	lsr x10, x10, #48
	sub x10, x10, x17
	mul x13, x2, x8
	madd x13, x3, x11, x13
	mul x16, x2, x10
	madd x16, x3, x9, x16
	lsr x2, x13, #15
	lsr x3, x16, #15
	orr x4, x8, x8
	orr x5, x11, x11
	orr x6, x10, x10
	orr x7, x9, x9
	movz x13, #32767, lsl #0
	and x8, x2, x13
	and x9, x3, x13
	movz x16, #32768, lsl #16
	add x8, x8, x16
	movz x16, #32768, lsl #32
	add x9, x9, x16
	movz x12, #1, lsl #0
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	movz x13, #16384, lsl #16
	movk x13, #8192, lsl #32
	movk x13, #8192, lsl #48
	movz x17, #16384, lsl #0
	add x8, x8, x13
	add x10, x10, x13
	lsr x11, x8, #47
	sub x11, x11, x17
	lsl x8, x8, #17
	lsr x8, x8, #48
	sub x8, x8, x17
	lsr x9, x10, #47
	sub x9, x9, x17
	lsl x10, x10, #17
	lsr x10, x10, #48
	sub x10, x10, x17
	mul x13, x2, x8
	madd x13, x3, x11, x13
	mul x16, x2, x10
	madd x16, x3, x9, x16
	lsr x2, x13, #15
	lsr x3, x16, #15
	mul x13, x8, x4
	madd x13, x11, x6, x13
	mul x16, x10, x4
	madd x6, x9, x6, x16
	mul x17, x8, x5
	madd x17, x11, x7, x17
	mul x16, x10, x5
	madd x7, x9, x7, x16
	orr x4, x13, x13
	orr x5, x17, x17
	movz x13, #32767, lsl #0
	and x8, x2, x13
	and x9, x3, x13
	movz x16, #32768, lsl #16
	add x8, x8, x16
	movz x16, #32768, lsl #32
	add x9, x9, x16
	movz x12, #1, lsl #0
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	movz x13, #16384, lsl #16
	movk x13, #8192, lsl #32
	movk x13, #8192, lsl #48
	movz x17, #16384, lsl #0
	add x8, x8, x13
	add x10, x10, x13
	lsr x11, x8, #47
	sub x11, x11, x17
	lsl x8, x8, #17
	lsr x8, x8, #48
	sub x8, x8, x17
	lsr x9, x10, #47
	sub x9, x9, x17
	lsl x10, x10, #17
	lsr x10, x10, #48
	sub x10, x10, x17
	mul x13, x2, x8
	madd x13, x3, x11, x13
	mul x16, x2, x10
	madd x16, x3, x9, x16
	lsr x2, x13, #15
	lsr x3, x16, #15
	mul x13, x8, x4
	madd x13, x11, x6, x13
	mul x16, x10, x4
	madd x6, x9, x6, x16
	mul x17, x8, x5
	madd x17, x11, x7, x17
	mul x16, x10, x5
	madd x7, x9, x7, x16
	orr x4, x13, x13
	orr x5, x17, x17
	movz x13, #32767, lsl #0
	and x8, x2, x13
	and x9, x3, x13
	movz x16, #32768, lsl #16
	add x8, x8, x16
	movz x16, #32768, lsl #32
	add x9, x9, x16
	movz x12, #1, lsl #0
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	movz x13, #16384, lsl #16
	movk x13, #8192, lsl #32
	movk x13, #8192, lsl #48
	movz x17, #16384, lsl #0
	add x8, x8, x13
	add x9, x9, x13
	lsr x11, x8, #47
	sub x11, x11, x17
	lsl x8, x8, #17
	lsr x8, x8, #48
	sub x8, x8, x17
	lsr x10, x9, #47
	sub x10, x10, x17
	lsl x9, x9, #17
	lsr x9, x9, #48
	sub x9, x9, x17
	mul x13, x8, x4
	madd x13, x11, x6, x13
	mul x16, x9, x4
	madd x6, x10, x6, x16
	mul x17, x8, x5
	madd x17, x11, x7, x17
	mul x16, x9, x5
	madd x7, x10, x7, x16
	orr x4, x13, x13
	orr x5, x17, x17
	movz x13, #0, lsl #0
	sub x1, x13, x1
	sub x1, x1, #1
	str x1, [x0, #480]
	movz x12, #0, lsl #0
	lsr x14, x4, #63
	sub x14, x12, x14
	eor x4, x4, x14
	sub x4, x4, x14
	lsr x15, x5, #63
	sub x15, x12, x15
	eor x5, x5, x15
	sub x5, x5, x15
	lsr x16, x6, #63
	sub x16, x12, x16
	eor x6, x6, x16
	sub x6, x6, x16
	lsr x17, x7, #63
	sub x17, x12, x17
	eor x7, x7, x17
	sub x7, x7, x17
	and x8, x4, x14
	and x9, x5, x15
	add x13, x8, x9
	and x8, x6, x16
	and x9, x7, x17
	add x11, x8, x9
	ldr x8, [x0, #192]
	eor x8, x8, x14
	mul x9, x8, x4
	umulh x10, x8, x4
	adds x1, x13, x9
	adc x2, x12, x10
	ldr x8, [x0, #224]
	eor x8, x8, x15
	mul x9, x8, x5
	umulh x10, x8, x5
	adds x1, x1, x9
	adc x2, x2, x10
	str x1, [x0, #320]
	ldr x8, [x0, #200]
	eor x8, x8, x14
	mul x9, x8, x4
	umulh x10, x8, x4
	adds x1, x2, x9
	adc x2, x12, x10
	ldr x8, [x0, #232]
	eor x8, x8, x15
	mul x9, x8, x5
	umulh x10, x8, x5
	adds x1, x1, x9
	adc x2, x2, x10
	str x1, [x0, #328]
	ldr x8, [x0, #208]
	eor x8, x8, x14
	mul x9, x8, x4
	umulh x10, x8, x4
	adds x1, x2, x9
	adc x2, x12, x10
	ldr x8, [x0, #240]
	eor x8, x8, x15
	mul x9, x8, x5
	umulh x10, x8, x5
	adds x1, x1, x9
	adc x2, x2, x10
	str x1, [x0, #336]
	ldr x8, [x0, #216]
	eor x8, x8, x14
	lsr x3, x8, #63
	sub x3, x12, x3
	and x3, x3, x4
	sub x3, x12, x3
	mul x9, x8, x4
	umulh x10, x8, x4
	adds x1, x2, x9
	adc x3, x3, x10
	ldr x8, [x0, #248]
	eor x8, x8, x15
	lsr x2, x8, #63
	sub x2, x12, x2
	and x2, x2, x5
	sub x2, x12, x2
	add x3, x3, x2
	mul x9, x8, x5
	umulh x10, x8, x5
	adds x1, x1, x9
	adc x3, x3, x10
	str x1, [x0, #344]
	str x3, [x0, #352]
	ldr x8, [x0, #192]
	eor x8, x8, x16
	mul x9, x8, x6
	umulh x10, x8, x6
	adds x1, x11, x9
	adc x2, x12, x10
	ldr x8, [x0, #224]
	eor x8, x8, x17
	mul x9, x8, x7
	umulh x10, x8, x7
	adds x1, x1, x9
	adc x2, x2, x10
	str x1, [x0, #360]
	ldr x8, [x0, #200]
	eor x8, x8, x16
	mul x9, x8, x6
	umulh x10, x8, x6
	adds x1, x2, x9
	adc x2, x12, x10
	ldr x8, [x0, #232]
	eor x8, x8, x17
	mul x9, x8, x7
	umulh x10, x8, x7
	adds x1, x1, x9
	adc x2, x2, x10
	str x1, [x0, #368]
	ldr x8, [x0, #208]
	eor x8, x8, x16
	mul x9, x8, x6
	umulh x10, x8, x6
	adds x1, x2, x9
	adc x2, x12, x10
	ldr x8, [x0, #240]
	eor x8, x8, x17
	mul x9, x8, x7
	umulh x10, x8, x7
	adds x1, x1, x9
	adc x2, x2, x10
	str x1, [x0, #376]
	ldr x8, [x0, #216]
	eor x8, x8, x16
	lsr x3, x8, #63
	sub x3, x12, x3
	and x3, x3, x6
	sub x3, x12, x3
	mul x9, x8, x6
	umulh x10, x8, x6
	adds x1, x2, x9
	adc x3, x3, x10
	ldr x8, [x0, #248]
	eor x8, x8, x17
	lsr x2, x8, #63
	sub x2, x12, x2
	and x2, x2, x7
	sub x2, x12, x2
	add x3, x3, x2
	mul x9, x8, x7
	umulh x10, x8, x7
	adds x1, x1, x9
	adc x3, x3, x10
	str x1, [x0, #384]
	str x3, [x0, #392]
	ldr x8, [x0, #256]
	eor x8, x8, x14
	mul x9, x8, x4
	umulh x10, x8, x4
	adds x1, x13, x9
	adc x2, x12, x10
	ldr x8, [x0, #288]
	eor x8, x8, x15
	mul x9, x8, x5
	umulh x10, x8, x5
	adds x1, x1, x9
	adc x2, x2, x10
	str x1, [x0, #400]
	ldr x8, [x0, #264]
	eor x8, x8, x14
	mul x9, x8, x4
	umulh x10, x8, x4
	adds x1, x2, x9
	adc x2, x12, x10
	ldr x8, [x0, #296]
	eor x8, x8, x15
	mul x9, x8, x5
	umulh x10, x8, x5
	adds x1, x1, x9
	adc x2, x2, x10
	str x1, [x0, #408]
	ldr x8, [x0, #272]
	eor x8, x8, x14
	mul x9, x8, x4
	umulh x10, x8, x4
	adds x1, x2, x9
	adc x2, x12, x10
	ldr x8, [x0, #304]
	eor x8, x8, x15
	mul x9, x8, x5
	umulh x10, x8, x5
	adds x1, x1, x9
	adc x2, x2, x10
	str x1, [x0, #416]
	ldr x8, [x0, #280]
	eor x8, x8, x14
	and x3, x14, x4
	sub x3, x12, x3
	mul x9, x8, x4
	umulh x10, x8, x4
	adds x1, x2, x9
	adc x3, x3, x10
	ldr x8, [x0, #312]
	eor x8, x8, x15
	and x2, x15, x5
	sub x2, x12, x2
	add x3, x3, x2
	mul x9, x8, x5
	umulh x10, x8, x5
	adds x1, x1, x9
	adc x3, x3, x10
	str x1, [x0, #424]
	str x3, [x0, #432]
	ldr x8, [x0, #256]
	eor x8, x8, x16
	mul x9, x8, x6
	umulh x10, x8, x6
	adds x1, x11, x9
	adc x2, x12, x10
	ldr x8, [x0, #288]
	eor x8, x8, x17
	mul x9, x8, x7
	umulh x10, x8, x7
	adds x1, x1, x9
	adc x2, x2, x10
	str x1, [x0, #440]
	ldr x8, [x0, #264]
	eor x8, x8, x16
	mul x9, x8, x6
	umulh x10, x8, x6
	adds x1, x2, x9
	adc x2, x12, x10
	ldr x8, [x0, #296]
	eor x8, x8, x17
	mul x9, x8, x7
	umulh x10, x8, x7
	adds x1, x1, x9
	adc x2, x2, x10
	str x1, [x0, #448]
	ldr x8, [x0, #272]
	eor x8, x8, x16
	mul x9, x8, x6
	umulh x10, x8, x6
	adds x1, x2, x9
	adc x2, x12, x10
	ldr x8, [x0, #304]
	eor x8, x8, x17
	mul x9, x8, x7
	umulh x10, x8, x7
	adds x1, x1, x9
	adc x2, x2, x10
	str x1, [x0, #456]
	ldr x8, [x0, #280]
	eor x8, x8, x16
	and x3, x16, x6
	sub x3, x12, x3
	mul x9, x8, x6
	umulh x10, x8, x6
	adds x1, x2, x9
	adc x3, x3, x10
	ldr x8, [x0, #312]
	eor x8, x8, x17
	and x2, x17, x7
	sub x2, x12, x2
	add x3, x3, x2
	mul x9, x8, x7
	umulh x10, x8, x7
	adds x1, x1, x9
	adc x3, x3, x10
	str x1, [x0, #464]
	str x3, [x0, #472]
	ldr x1, [x0, #320]
	ldr x2, [x0, #328]
	ldr x3, [x0, #336]
	ldr x8, [x0, #344]
	ldr x9, [x0, #352]
	extr x1, x2, x1, #59
	extr x2, x3, x2, #59
	extr x3, x8, x3, #59
	extr x8, x9, x8, #59
	str x1, [x0, #192]
	str x2, [x0, #200]
	str x3, [x0, #208]
	str x8, [x0, #216]
	ldr x1, [x0, #360]
	ldr x2, [x0, #368]
	ldr x3, [x0, #376]
	ldr x8, [x0, #384]
	ldr x9, [x0, #392]
	extr x1, x2, x1, #59
	extr x2, x3, x2, #59
	extr x3, x8, x3, #59
	extr x8, x9, x8, #59
	str x1, [x0, #224]
	str x2, [x0, #232]
	str x3, [x0, #240]
	str x8, [x0, #248]
	movz x13, #19, lsl #0
	ldr x1, [x0, #400]
	ldr x2, [x0, #408]
	ldr x3, [x0, #416]
	ldr x8, [x0, #424]
	ldr x9, [x0, #432]
	extr x10, x9, x8, #63
	lsr x11, x9, #63
	sub x10, x10, x11
	lsl x11, x10, #63
	add x8, x8, x11
	lsr x14, x10, #63
	sub x14, x12, x14
	mul x9, x10, x13
	umulh x11, x10, x13
	and x15, x14, x13
	sub x11, x11, x15
	adds x1, x1, x9
	adcs x2, x2, x11
	adcs x3, x3, x14
	adc x8, x8, x14
	str x1, [x0, #256]
	str x2, [x0, #264]
	str x3, [x0, #272]
	str x8, [x0, #280]
	ldr x1, [x0, #440]
	ldr x2, [x0, #448]
	ldr x3, [x0, #456]
	ldr x8, [x0, #464]
	ldr x9, [x0, #472]
	extr x10, x9, x8, #63
	lsr x11, x9, #63
	sub x10, x10, x11
	lsl x11, x10, #63
	add x8, x8, x11
	lsr x14, x10, #63
	sub x14, x12, x14
	mul x9, x10, x13
	umulh x11, x10, x13
	and x15, x14, x13
	sub x11, x11, x15
	adds x1, x1, x9
	adcs x2, x2, x11
	adcs x3, x3, x14
	adc x8, x8, x14
	str x1, [x0, #288]
	str x2, [x0, #296]
	str x3, [x0, #304]
	str x8, [x0, #312]
	sub x20, x20, #1
	cbnz x20, 21b
	movz x12, #0, lsl #0
	movz x6, #19, lsl #0
	movz x7, #65535, lsl #0
	movk x7, #65535, lsl #16
	movk x7, #65535, lsl #32
	movk x7, #32767, lsl #48
	ldr x2, [x0, #256]
	ldr x3, [x0, #264]
	ldr x4, [x0, #272]
	ldr x5, [x0, #280]
	lsr x8, x5, #63
	and x5, x5, x7
	mul x8, x8, x6
	adds x2, x2, x8
	adcs x3, x3, x12
	adcs x4, x4, x12
	adc x5, x5, x12
	movz x9, #65498, lsl #0
	movk x9, #65535, lsl #16
	movk x9, #65535, lsl #32
	movk x9, #65535, lsl #48
	movz x10, #65535, lsl #0
	movk x10, #65535, lsl #16
	movk x10, #65535, lsl #32
	movk x10, #65535, lsl #48
	subs x8, x9, x2
	sbcs x9, x10, x3
	sbcs x11, x10, x4
	sbc x10, x10, x5
	ldr x13, [x0, #216]
	lsr x13, x13, #63
	sub x13, x12, x13
	eor x8, x8, x2
	and x8, x8, x13
	eor x2, x2, x8
	eor x9, x9, x3
	and x9, x9, x13
	eor x3, x3, x9
	eor x11, x11, x4
	and x11, x11, x13
	eor x4, x4, x11
	eor x10, x10, x5
	and x10, x10, x13
	eor x5, x5, x10
	str x2, [x0, #544]
	str x3, [x0, #552]
	str x4, [x0, #560]
	str x5, [x0, #568]
	add x1, x19, #0
	movz w10, #0, lsl #0
	ldr x12, [x0, #544]
	ldr x13, [x0, #552]
	ldr x14, [x0, #560]
	ldr x15, [x0, #568]
	ldr x3, [x0, #96]
	mul x4, x3, x12
	mul x5, x3, x13
	mul x6, x3, x14
	mul x7, x3, x15
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adc x21, x16, x10
	ldr x3, [x0, #104]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adc x22, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adc x22, x22, x16
	ldr x3, [x0, #112]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	adc x23, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adc x23, x23, x16
	ldr x3, [x0, #120]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	adc x24, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x21, x21, x2
	adcs x22, x22, x8
	adcs x23, x23, x9
	adc x24, x24, x16
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adc x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adc x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adc x7, x7, x10
	str x4, [x0, #96]
	str x5, [x0, #104]
	str x6, [x0, #112]
	str x7, [x0, #120]
	movz w10, #0, lsl #0
	movz w11, #19, lsl #0
	movz x2, #65535, lsl #0
	movk x2, #65535, lsl #16
	movk x2, #65535, lsl #32
	movk x2, #32767, lsl #48
	ldr x4, [x0, #96]
	ldr x5, [x0, #104]
	ldr x6, [x0, #112]
	ldr x7, [x0, #120]
	lsr x8, x7, #63
	and x7, x7, x2
	mul x3, x8, x11
	adds x4, x4, x3
	adcs x5, x5, x10
	adcs x6, x6, x10
	adcs x7, x7, x10
	adds x21, x4, x11
	adcs x22, x5, x10
	adcs x23, x6, x10
	adcs x24, x7, x10
	lsr x8, x24, #63
	and x24, x24, x2
	sub x3, x10, x8
	eor x21, x21, x4
	and x21, x21, x3
	eor x4, x4, x21
	eor x22, x22, x5
	and x22, x22, x3
	eor x5, x5, x22
	eor x23, x23, x6
	and x23, x23, x3
	eor x6, x6, x23
	eor x24, x24, x7
	and x24, x24, x3
	eor x7, x7, x24
	str x4, [x1, #0]
	str x5, [x1, #8]
	str x6, [x1, #16]
	str x7, [x1, #24]
	ldr x19, [x0, #0]
	ldr x20, [x0, #8]
	ldr x21, [x0, #16]
	ldr x22, [x0, #24]
	ldr x23, [x0, #32]
	ldr x24, [x0, #40]
	ret
	.p2align 6
