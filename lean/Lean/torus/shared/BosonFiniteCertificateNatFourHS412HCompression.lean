import torus.shared.BosonFiniteCertificateNatFourHS412HSource

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2
open Matrix
open scoped BigOperators

private def f412HCompressionInteger : Matrix (Fin 34) (Fin 34) ℤ :=
  !![34504955100, 5613300, 5613300, 5613300, 5613300, 5613300, 5613300, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    5613300, 960498000, 1871100, 1871100, 1871100, 1871100, 1871100, 623700, 311850, 311850, 311850, 311850, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    5613300, 1871100, 118219500, 1871100, 1871100, 1871100, 1871100, 29030400, 113400, 0, 0, 0, 226800, 113400, 113400, 113400, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    5613300, 1871100, 1871100, 28134540, 1871100, 1871100, 1871100, 0, 4354560, 68040, 0, 0, 0, 68040, 0, 0, 136080, 68040, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    5613300, 1871100, 1871100, 1871100, 11668860, 1871100, 1871100, 0, 0, 967680, 60480, 0, 967680, 0, 60480, 0, 0, 60480, 181440, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    5613300, 1871100, 1871100, 1871100, 1871100, 7465500, 1871100, 0, 0, 0, 302400, 75600, 0, 302400, 0, 151200, 0, 75600, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    5613300, 1871100, 1871100, 1871100, 1871100, 1871100, 11202300, 0, 0, 0, 0, 259200, 0, 0, 259200, 0, 259200, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 623700, 29030400, 0, 0, 0, 0, 73256400, 311850, 311850, 311850, 311850, 0, 0, 0, 0, 0, 0, 0, 170100, 56700, 56700, 56700, 56700, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 311850, 113400, 4354560, 0, 0, 0, 311850, 6755805, 155925, 155925, 155925, 113400, 56700, 56700, 56700, 0, 0, 0, 4354560, 22680, 0, 0, 0, 22680, 11340, 11340, 0, 0, 0, 0, 0, 0, 0;
    0, 311850, 0, 68040, 967680, 0, 0, 311850, 155925, 1890945, 155925, 155925, 483840, 34020, 0, 0, 68040, 34020, 0, 0, 483840, 15120, 0, 0, 0, 7560, 0, 15120, 7560, 0, 0, 0, 0, 0;
    0, 311850, 0, 0, 60480, 302400, 0, 311850, 155925, 155925, 889245, 155925, 0, 151200, 30240, 0, 0, 30240, 90720, 0, 0, 120960, 15120, 0, 60480, 0, 7560, 0, 15120, 0, 0, 0, 0, 0;
    0, 311850, 0, 0, 0, 75600, 259200, 311850, 155925, 155925, 155925, 636525, 0, 0, 64800, 75600, 64800, 37800, 0, 0, 0, 0, 43200, 43200, 0, 21600, 10800, 10800, 0, 0, 0, 0, 0, 0;
    0, 0, 226800, 0, 967680, 0, 0, 0, 113400, 483840, 0, 0, 2010960, 113400, 113400, 113400, 0, 0, 0, 0, 645120, 0, 0, 0, 10080, 0, 0, 0, 0, 30240, 10080, 10080, 0, 0;
    0, 0, 113400, 68040, 0, 302400, 0, 0, 56700, 34020, 151200, 0, 113400, 427140, 56700, 56700, 68040, 34020, 0, 0, 0, 120960, 0, 0, 120960, 3780, 0, 0, 0, 0, 7560, 0, 7560, 0;
    0, 0, 113400, 0, 60480, 0, 259200, 0, 56700, 0, 30240, 64800, 113400, 56700, 242460, 56700, 64800, 30240, 90720, 0, 0, 0, 69120, 0, 0, 17280, 4320, 0, 0, 51840, 0, 17280, 4320, 0;
    0, 0, 113400, 0, 0, 151200, 0, 0, 56700, 0, 0, 75600, 113400, 56700, 56700, 351900, 0, 75600, 0, 0, 0, 0, 0, 115200, 0, 0, 14400, 0, 0, 0, 28800, 0, 0, 0;
    0, 0, 0, 136080, 0, 0, 259200, 0, 0, 68040, 0, 64800, 0, 68040, 64800, 0, 311040, 68040, 0, 0, 0, 0, 0, 0, 0, 51840, 0, 6480, 0, 0, 0, 0, 6480, 38880;
    0, 0, 0, 68040, 60480, 75600, 0, 0, 0, 34020, 30240, 37800, 0, 34020, 30240, 75600, 68040, 132300, 90720, 0, 0, 0, 0, 0, 0, 0, 17280, 17280, 8640, 0, 8640, 0, 8640, 0;
    0, 0, 0, 0, 181440, 0, 0, 0, 0, 0, 90720, 0, 0, 0, 90720, 0, 0, 90720, 396576, 0, 0, 0, 0, 0, 0, 0, 0, 0, 41472, 0, 0, 41472, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 170100, 4354560, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13573980, 170100, 170100, 170100, 170100, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 56700, 22680, 483840, 0, 0, 645120, 0, 0, 0, 0, 0, 0, 170100, 1392300, 56700, 56700, 56700, 45360, 22680, 22680, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 56700, 0, 15120, 120960, 0, 0, 120960, 0, 0, 0, 0, 0, 170100, 56700, 449820, 56700, 56700, 120960, 15120, 0, 30240, 15120, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 56700, 0, 0, 15120, 43200, 0, 0, 69120, 0, 0, 0, 0, 170100, 56700, 56700, 242460, 56700, 0, 43200, 15120, 0, 30240, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 56700, 0, 0, 0, 43200, 0, 0, 0, 115200, 0, 0, 0, 170100, 56700, 56700, 56700, 344700, 0, 0, 43200, 43200, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 22680, 0, 60480, 0, 10080, 120960, 0, 0, 0, 0, 0, 0, 45360, 120960, 0, 0, 357840, 22680, 22680, 0, 0, 30240, 10080, 10080, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 11340, 7560, 0, 21600, 0, 3780, 17280, 0, 51840, 0, 0, 0, 22680, 15120, 43200, 0, 22680, 87480, 11340, 15120, 7560, 51840, 7560, 0, 7560, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 11340, 0, 7560, 10800, 0, 0, 4320, 14400, 0, 17280, 0, 0, 22680, 0, 15120, 43200, 22680, 11340, 58500, 10800, 15120, 0, 14400, 17280, 4320, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 15120, 0, 10800, 0, 0, 0, 0, 6480, 17280, 0, 0, 0, 30240, 0, 43200, 0, 15120, 10800, 82080, 15120, 0, 17280, 0, 6480, 38880;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 7560, 15120, 0, 0, 0, 0, 0, 0, 8640, 41472, 0, 0, 15120, 30240, 0, 0, 7560, 15120, 15120, 68904, 0, 0, 13824, 17280, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 30240, 0, 51840, 0, 0, 0, 0, 0, 0, 0, 0, 0, 30240, 51840, 0, 0, 0, 246240, 30240, 30240, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10080, 7560, 0, 28800, 0, 8640, 0, 0, 0, 0, 0, 0, 10080, 7560, 14400, 17280, 0, 30240, 62640, 10080, 15120, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10080, 0, 17280, 0, 0, 0, 41472, 0, 0, 0, 0, 0, 10080, 0, 17280, 0, 13824, 30240, 10080, 93024, 17280, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7560, 4320, 0, 6480, 8640, 0, 0, 0, 0, 0, 0, 0, 7560, 4320, 6480, 17280, 0, 15120, 17280, 43200, 38880;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 38880, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 38880, 0, 0, 0, 0, 38880, 233280]

private def f412HCompressionCoordinates : Matrix (Fin 34) (Fin 7) ℤ :=
  !![15, (-15), 21, (-15), 21, 21, (-42);
    (-180), 180, (-252), 180, (-252), (-252), 504;
    990, (-495), 594, (-440), 429, 374, (-693);
    (-3300), 825, (-660), 825, (-363), (-264), 330;
    7425, (-825), 297, (-825), 99, 99, 0;
    (-11880), 330, 0, 330, 0, 0, 0;
    6930, 0, 0, 0, 0, 0, 0;
    0, (-495), 792, (-550), 957, 1012, (-2079);
    0, 2475, (-3960), 1925, (-3201), (-2948), 5940;
    0, (-4125), 4752, (-4125), 2871, 1980, (-2970);
    0, 4950, (-2376), 4950, (-792), (-792), 0;
    0, (-2310), 0, (-2310), 0, 0, 0;
    0, (-2475), 5346, 0, 2673, 1980, (-4455);
    0, 6600, (-14256), 0, (-5148), (-2112), 4752;
    0, (-11550), 8316, 0, 1386, 924, 0;
    0, 6930, 0, 0, 0, 0, 0;
    0, 0, 11088, 0, 2772, 0, (-1386);
    0, 0, (-16632), 0, (-1386), 0, 0;
    0, 0, 6930, 0, 0, 0, 0;
    0, 0, 0, 550, (-1056), (-1408), 2970;
    0, 0, 0, (-2475), 4752, 6336, (-13365);
    0, 0, 0, 6600, (-4752), (-4224), 7128;
    0, 0, 0, (-11550), 1386, 1848, 0;
    0, 0, 0, 6930, 0, 0, 0;
    0, 0, 0, 0, (-5940), (-9504), 21384;
    0, 0, 0, 0, 13860, 11088, (-24948);
    0, 0, 0, 0, (-4158), (-5544), 0;
    0, 0, 0, 0, (-11088), 0, 8316;
    0, 0, 0, 0, 6930, 0, 0;
    0, 0, 0, 0, 0, 5544, (-12474);
    0, 0, 0, 0, 0, (-11088), 24948;
    0, 0, 0, 0, 0, 6930, 0;
    0, 0, 0, 0, 0, 0, (-20790);
    0, 0, 0, 0, 0, 0, 6930]

private def f412HCompressionLeftProduct : Matrix (Fin 7) (Fin 34) ℤ :=
  !![517490127000, (-172496709000), 115241049000, (-86613219000), 72804501000, (-66405339000), 64721349000, 28627830000, (-14313915000), 6904359000, (-3199581000), 841995000, 7409556000, (-3704778000), 2357586000, (-1683990000), 1347192000, (-673596000), 1347192000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    (-517490127000), 172496709000, (-72074772000), 32557140000, (-14925141000), 6155919000, (-3648645000), (-50210968500), 19758816000, (-8815999500), 4384611000, (-1253637000), (-7378371000), 3124737000, (-2279623500), 1836796500, (-617463000), 352390500, (-748440000), 10693336500, (-3564445500), 1306651500, (-851350500), 670477500, 1128897000, (-227650500), 90436500, (-87318000), 43659000, (-673596000), 224532000, (-224532000), 0, 0;
    724486177800, (-241495392600), 92271425400, (-34768780200), 13370880600, (-6208309800), 5108103000, 74611983600, (-28751322600), 10698949800, (-3581285400), 550103400, 12349260000, (-5222614320), 2447398800, (-1145113200), 2119582080, (-987940800), 1832181120, (-17109338400), 5703112800, (-1895050080), 583783200, 44906400, (-1904031360), 655633440, (-314344800), (-143700480), 143700480, 592764480, (-197588160), 484989120, (-143700480), 431101440;
    (-517181395500), 172393798500, (-66894943500), 29815978500, (-11728678500), 3215173500, (-551974500), (-52749427500), 18539482500, (-9043650000), 4256752500, (-1331599500), (-4272345000), 1621620000, (-788980500), 732847500, (-318087000), (-46777500), 299376000, 15670462500, (-5223487500), 3165277500, (-2136172500), 1930351500, 1029105000, (-514552500), 102910500, 411642000, (-205821000), 0, 0, 0, 0, 0;
    724115700000, (-241371900000), 77467282200, (-23389498440), 6241989600, (-1945944000), 1032847200, 81952308900, (-27038891880), 8573754420, (-2148022800), 456548400, 9173629080, (-3096296280), 651517020, (-207692100), 1300040280, (-276548580), 233513280, (-27874525140), 9291508380, (-3329435340), 1039957380, (-705404700), (-2981036520), 1144738980, (-167276340), (-746943120), 319583880, 691558560, (-230519520), 14968800, 107775360, (-323326080);
    724362685200, (-241454228400), 72910530000, (-19742350320), 4847396400, (-840747600), 276922800, 84271849200, (-26584089840), 7447476960, (-2003324400), 281912400, 8768723040, (-2522741760), 888647760, (-366735600), 589770720, (-204074640), 317338560, (-31103669520), 10367889840, (-2921410800), 832764240, (-197089200), (-3723239520), 1044323280, (-317837520), (-181621440), 90810720, 1634592960, (-544864320), 544864320, 0, 0;
    (-1448416638900), 482805546300, (-140753497500), 34493728500, (-7156957500), 1465071300, (-331184700), (-171026024400), 53129884500, (-13668385500), 2845943100, (-566943300), (-17872747200), 4995837000, (-1234926000), 740955600, (-1369645200), 168399000, 0, 64766255400, (-21588751800), 5826605400, (-1044073800), 392931000, 7881073200, (-2391265800), 325571400, 1032847200, (-336798000), (-3098541600), 1032847200, (-314344800), (-359251200), 1077753600]

private def f412HCompressionResult : Matrix (Fin 7) (Fin 7) ℤ :=
  !![2216711816550000, (-426840945300000), 468854811810000, (-332514210105000), 284808850326000, 239557456908000, (-434647080945000);
    (-426840945300000), 328359713220000, (-414235269756000), 276153216570000, (-324389463552000), (-310938649560000), 597688803558000;
    468854811810000, (-414235269756000), 603552968670960, (-338678174835000), 476398763683920, 448367672380320, (-873169325998200);
    (-332514210105000), 276153216570000, (-338678174835000), 310198239697500, (-334861841853000), (-318817340226000), 615817825969500;
    284808850326000, (-324389463552000), 476398763683920, (-334861841853000), 490638547198800, 480975975738720, (-975381928151400);
    239557456908000, (-310938649560000), 448367672380320, (-318817340226000), 480975975738720, 503486020255680, (-1009191608686800);
    (-434647080945000), 597688803558000, (-873169325998200), 615817825969500, (-975381928151400), (-1009191608686800), 2068657116579900]

theorem f412_relative_H_compression :
    b412relativeᵀ*f412rawHForm*b412relative=b412h := by
  have hM : natFourIntegerMatrix 4 f412HCompressionInteger=f412rawHForm := by
    ext a b
    fin_cases a
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix 4 f412HCompressionInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawHForm) 0 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix 4 f412HCompressionInteger) 1 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawHForm) 1 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix 4 f412HCompressionInteger) 2 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawHForm) 2 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix 4 f412HCompressionInteger) 3 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawHForm) 3 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix 4 f412HCompressionInteger) 4 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawHForm) 4 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix 4 f412HCompressionInteger) 5 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawHForm) 5 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix 4 f412HCompressionInteger) 6 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawHForm) 6 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix 4 f412HCompressionInteger) 7 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawHForm) 7 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix 4 f412HCompressionInteger) 8 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawHForm) 8 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix 4 f412HCompressionInteger) 9 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawHForm) 9 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix 4 f412HCompressionInteger) 10 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawHForm) 10 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix 4 f412HCompressionInteger) 11 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawHForm) 11 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix 4 f412HCompressionInteger) 12 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawHForm) 12 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix 4 f412HCompressionInteger) 13 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawHForm) 13 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix 4 f412HCompressionInteger) 14 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawHForm) 14 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix 4 f412HCompressionInteger) 15 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawHForm) 15 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix 4 f412HCompressionInteger) 16 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawHForm) 16 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix 4 f412HCompressionInteger) 17 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawHForm) 17 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix 4 f412HCompressionInteger) 18 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawHForm) 18 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix 4 f412HCompressionInteger) 19 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawHForm) 19 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix 4 f412HCompressionInteger) 20 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawHForm) 20 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix 4 f412HCompressionInteger) 21 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawHForm) 21 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix 4 f412HCompressionInteger) 22 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawHForm) 22 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix 4 f412HCompressionInteger) 23 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawHForm) 23 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix 4 f412HCompressionInteger) 24 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawHForm) 24 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix 4 f412HCompressionInteger) 25 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawHForm) 25 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix 4 f412HCompressionInteger) 26 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawHForm) 26 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix 4 f412HCompressionInteger) 27 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawHForm) 27 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix 4 f412HCompressionInteger) 28 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawHForm) 28 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix 4 f412HCompressionInteger) 29 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawHForm) 29 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix 4 f412HCompressionInteger) 30 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawHForm) 30 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix 4 f412HCompressionInteger) 31 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawHForm) 31 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix 4 f412HCompressionInteger) 32 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawHForm) 32 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix 4 f412HCompressionInteger) 33 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawHForm) 33 j) (by decide +kernel)
      exact h 0 b
  have hD : natFourIntegerMatrix 6930 f412HCompressionCoordinates=b412relative := by
    ext a b
    fin_cases a
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 6930 f412HCompressionCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 7) => (b412relative) 0 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 6930 f412HCompressionCoordinates) 1 j)
        (fun (_ : Fin 1) (j : Fin 7) => (b412relative) 1 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 6930 f412HCompressionCoordinates) 2 j)
        (fun (_ : Fin 1) (j : Fin 7) => (b412relative) 2 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 6930 f412HCompressionCoordinates) 3 j)
        (fun (_ : Fin 1) (j : Fin 7) => (b412relative) 3 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 6930 f412HCompressionCoordinates) 4 j)
        (fun (_ : Fin 1) (j : Fin 7) => (b412relative) 4 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 6930 f412HCompressionCoordinates) 5 j)
        (fun (_ : Fin 1) (j : Fin 7) => (b412relative) 5 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 6930 f412HCompressionCoordinates) 6 j)
        (fun (_ : Fin 1) (j : Fin 7) => (b412relative) 6 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 6930 f412HCompressionCoordinates) 7 j)
        (fun (_ : Fin 1) (j : Fin 7) => (b412relative) 7 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 6930 f412HCompressionCoordinates) 8 j)
        (fun (_ : Fin 1) (j : Fin 7) => (b412relative) 8 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 6930 f412HCompressionCoordinates) 9 j)
        (fun (_ : Fin 1) (j : Fin 7) => (b412relative) 9 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 6930 f412HCompressionCoordinates) 10 j)
        (fun (_ : Fin 1) (j : Fin 7) => (b412relative) 10 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 6930 f412HCompressionCoordinates) 11 j)
        (fun (_ : Fin 1) (j : Fin 7) => (b412relative) 11 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 6930 f412HCompressionCoordinates) 12 j)
        (fun (_ : Fin 1) (j : Fin 7) => (b412relative) 12 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 6930 f412HCompressionCoordinates) 13 j)
        (fun (_ : Fin 1) (j : Fin 7) => (b412relative) 13 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 6930 f412HCompressionCoordinates) 14 j)
        (fun (_ : Fin 1) (j : Fin 7) => (b412relative) 14 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 6930 f412HCompressionCoordinates) 15 j)
        (fun (_ : Fin 1) (j : Fin 7) => (b412relative) 15 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 6930 f412HCompressionCoordinates) 16 j)
        (fun (_ : Fin 1) (j : Fin 7) => (b412relative) 16 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 6930 f412HCompressionCoordinates) 17 j)
        (fun (_ : Fin 1) (j : Fin 7) => (b412relative) 17 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 6930 f412HCompressionCoordinates) 18 j)
        (fun (_ : Fin 1) (j : Fin 7) => (b412relative) 18 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 6930 f412HCompressionCoordinates) 19 j)
        (fun (_ : Fin 1) (j : Fin 7) => (b412relative) 19 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 6930 f412HCompressionCoordinates) 20 j)
        (fun (_ : Fin 1) (j : Fin 7) => (b412relative) 20 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 6930 f412HCompressionCoordinates) 21 j)
        (fun (_ : Fin 1) (j : Fin 7) => (b412relative) 21 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 6930 f412HCompressionCoordinates) 22 j)
        (fun (_ : Fin 1) (j : Fin 7) => (b412relative) 22 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 6930 f412HCompressionCoordinates) 23 j)
        (fun (_ : Fin 1) (j : Fin 7) => (b412relative) 23 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 6930 f412HCompressionCoordinates) 24 j)
        (fun (_ : Fin 1) (j : Fin 7) => (b412relative) 24 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 6930 f412HCompressionCoordinates) 25 j)
        (fun (_ : Fin 1) (j : Fin 7) => (b412relative) 25 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 6930 f412HCompressionCoordinates) 26 j)
        (fun (_ : Fin 1) (j : Fin 7) => (b412relative) 26 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 6930 f412HCompressionCoordinates) 27 j)
        (fun (_ : Fin 1) (j : Fin 7) => (b412relative) 27 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 6930 f412HCompressionCoordinates) 28 j)
        (fun (_ : Fin 1) (j : Fin 7) => (b412relative) 28 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 6930 f412HCompressionCoordinates) 29 j)
        (fun (_ : Fin 1) (j : Fin 7) => (b412relative) 29 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 6930 f412HCompressionCoordinates) 30 j)
        (fun (_ : Fin 1) (j : Fin 7) => (b412relative) 30 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 6930 f412HCompressionCoordinates) 31 j)
        (fun (_ : Fin 1) (j : Fin 7) => (b412relative) 31 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 6930 f412HCompressionCoordinates) 32 j)
        (fun (_ : Fin 1) (j : Fin 7) => (b412relative) 32 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 6930 f412HCompressionCoordinates) 33 j)
        (fun (_ : Fin 1) (j : Fin 7) => (b412relative) 33 j) (by decide +kernel)
      exact h 0 b
  have hV : f412HCompressionCoordinatesᵀ*f412HCompressionInteger=f412HCompressionLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (f412HCompressionCoordinatesᵀ*f412HCompressionInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412HCompressionLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (f412HCompressionCoordinatesᵀ*f412HCompressionInteger) 1 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412HCompressionLeftProduct) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (f412HCompressionCoordinatesᵀ*f412HCompressionInteger) 2 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412HCompressionLeftProduct) 2 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (f412HCompressionCoordinatesᵀ*f412HCompressionInteger) 3 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412HCompressionLeftProduct) 3 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (f412HCompressionCoordinatesᵀ*f412HCompressionInteger) 4 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412HCompressionLeftProduct) 4 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (f412HCompressionCoordinatesᵀ*f412HCompressionInteger) 5 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412HCompressionLeftProduct) 5 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (f412HCompressionCoordinatesᵀ*f412HCompressionInteger) 6 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412HCompressionLeftProduct) 6 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f412HCompressionLeftProduct*f412HCompressionCoordinates=f412HCompressionResult := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (f412HCompressionLeftProduct*f412HCompressionCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 7) => (f412HCompressionResult) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (f412HCompressionLeftProduct*f412HCompressionCoordinates) 1 j)
        (fun (_ : Fin 1) (j : Fin 7) => (f412HCompressionResult) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (f412HCompressionLeftProduct*f412HCompressionCoordinates) 2 j)
        (fun (_ : Fin 1) (j : Fin 7) => (f412HCompressionResult) 2 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (f412HCompressionLeftProduct*f412HCompressionCoordinates) 3 j)
        (fun (_ : Fin 1) (j : Fin 7) => (f412HCompressionResult) 3 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (f412HCompressionLeftProduct*f412HCompressionCoordinates) 4 j)
        (fun (_ : Fin 1) (j : Fin 7) => (f412HCompressionResult) 4 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (f412HCompressionLeftProduct*f412HCompressionCoordinates) 5 j)
        (fun (_ : Fin 1) (j : Fin 7) => (f412HCompressionResult) 5 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (f412HCompressionLeftProduct*f412HCompressionCoordinates) 6 j)
        (fun (_ : Fin 1) (j : Fin 7) => (f412HCompressionResult) 6 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (6930*4*6930) f412HCompressionResult=b412h := by
    ext a b
    fin_cases a
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix (6930*4*6930) f412HCompressionResult) 0 j)
        (fun (_ : Fin 1) (j : Fin 7) => (b412h) 0 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix (6930*4*6930) f412HCompressionResult) 1 j)
        (fun (_ : Fin 1) (j : Fin 7) => (b412h) 1 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix (6930*4*6930) f412HCompressionResult) 2 j)
        (fun (_ : Fin 1) (j : Fin 7) => (b412h) 2 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix (6930*4*6930) f412HCompressionResult) 3 j)
        (fun (_ : Fin 1) (j : Fin 7) => (b412h) 3 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix (6930*4*6930) f412HCompressionResult) 4 j)
        (fun (_ : Fin 1) (j : Fin 7) => (b412h) 4 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix (6930*4*6930) f412HCompressionResult) 5 j)
        (fun (_ : Fin 1) (j : Fin 7) => (b412h) 5 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix (6930*4*6930) f412HCompressionResult) 6 j)
        (fun (_ : Fin 1) (j : Fin 7) => (b412h) 6 j) (by decide +kernel)
      exact h 0 b
  exact natFourIntegerMatrix_compression_check_staged 4 6930
    f412HCompressionInteger f412HCompressionCoordinates f412HCompressionLeftProduct f412HCompressionResult
    f412rawHForm b412relative b412h hM hD hV hY hF

theorem f412_actual_relative_H_form (x y : Fin 7 → ℂ) :
    natOccupationInner (natFourWordBlock f412basis (complexify b412relative *ᵥ x))
      (canonicalPairHamiltonianNat (natFourWordBlock f412basis (complexify b412relative *ᵥ y)))=
      star x ⬝ᵥ (complexify b412h *ᵥ y) :=
  natFour_operator_relative_matrix_form f412basis b412relative canonicalPairHamiltonianNat
    f412rawHForm b412h f412_actual_raw_H_matrix
    f412_relative_H_compression x y

#print axioms f412_relative_H_compression
#print axioms f412_actual_relative_H_form
end TorusLean.BosonFiniteCertificate
