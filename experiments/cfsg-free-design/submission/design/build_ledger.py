"""Generate the review-level planning ledger; does not generate or check Lean proofs."""
import json
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
# Dependencies are proposed delivery prerequisites, not a discovered Lean import graph.
DATA = '''
E00|工程|固定版本、完整依赖与源码审计||重建基线并记录工具链、导入闭包、定义及公理清单
E01|工程|证明与计算证书基础设施|E00|声明级依赖审计、重放器、资源度量与独立构建
F00|基础|有限section与阶归纳|E00|子群/正规商/section的同构运输、阶界与单群性质
F01|基础|p局部子群与有限秩|F00|O_p/O_pi、Hall、Sylow、elementary abelian秩及局部定义
F02|基础|幂零与广义Fitting|F01|Frattini、Fitting、layer、quasisimple、subnormal及中心积
F03|基础|互素作用与局部模|F02|交换子恒等式、固定点、replacement、critical subgroup
F04|基础|转移与融合|F01|transfer、normal complement、fusion与strong closure
R00|表示|普通特征标|F00|正交性、不可约分解、代数整数、诱导限制及Clifford理论
R01|表示|模表示与块|R00,F03|Brauer character、缺陷与块、所用分解数的独立证明
R02|表示|扩张与乘子工具|R00,F02|H1/H2、中心扩张、Schur multiplier的所需计算
A00|Lie|根群与积分模型|E00|全部所需正负根关系、生成、pinning及尚缺的群方案比较
A01|Lie|Steinberg固定点与有限域|A00,F00|保根保F同构、下降、固定点有限性及候选商运输
A02|Lie|BN-pair与阶公式|A01,F01|Bruhat分解、有限生成、中心、导群、阶公式与简单性准则
C00|名单|循环与交错群|F00|素数循环分类和交错群有限单性及固定载体桥
L01|Lie|经典A/C族|A02|A及twistedA、C的全参数有限单性与识别
L02|Lie|B/D与spin族|A02,R02|B、D、twistedD含坏特征、中心商及spin载体桥
L03|Lie|普通例外族|A02|E6/E7/E8/F4/G2的全参数结构与载体桥
L04|Lie|图扭曲例外族|L03,L02|twistedE6及trialityD4的保Steinberg比较及识别
L05|Lie|Suzuki/Ree/Tits|A02|三半Frobenius族及Tits导群的有限单性与比较
S00|散在|呈示与证书通用层|E01,F00|自由群商泛性质、Tietze及BSGS/陪集证书的健全性
S01|散在|Mathieu族|S00,F04|M11/M12/M22/M23/M24的构造、简单性、局部识别、呈示同构
S02|散在|Janko族|S00,R00,R02|J1/J2/J3/J4的有限模型、结构与各呈示上下界
S03|散在|Conway与Suz|S00,R00|格及有限几何构造Co1/Co2/Co3/Suz与呈示识别
S04|散在|图与局部几何六族|S00,R00|HS/McL/He/Ru/ON/Ly的模型、局部识别与呈示识别
S05|散在|Fischer族|S00,R01|三换位结构Fi22/Fi23/Fi24prime及派生/中心问题
S06|散在|HN/Th与Baby Monster|S00,R01,R02|HN/Th/B的存在、有限单性及精确呈示同构
S07|散在|Monster|S00,S03,S06,R02|独立有限模型、存在/唯一性、Y443中心关系与80关系目标同构
N00|名单|小同构正规化|C00,L01,L02,L03,L04,L05|六重复项及低秩/小域导群例外归到有效index
K00|已知族|全部已知族的局部结构表|C00,L01,L02,L03,L04,L05,S01,S02,S03,S04,S05,S06,S07,R01,R02|所需Aut/Out、乘子、involution中心化子、局部模与子群表逐项独立证明
I00|归纳|K群与K-proper接口|F00|仅从较小单section已分类推出真子群K性，明示card严格下降
O00|奇数阶|极小反例局部理论|F02,F03,F04|奇数阶极小非可解群、Hall系统、极大子群及TI/Frobenius结构
O01|奇数阶|特征标与数论矛盾|O00,R00|exceptional characters、诱导等距及所需数论引理
O02|奇数阶|Feit-Thompson收口|O01|任意有限奇数阶群可解及非阿贝尔有限单群偶数阶
T00|局部分类|低2秩与强嵌入|F02,F04,R01,I00,K00|低秩各Sylow形状、转移、强嵌入及相应族识别
T01|局部分类|可解signalizer|F02,F03,F04|theta函数平衡、完备性与连接性
T02|局部分类|非可解signalizer|T01,I00,K00|K群假设下signalizer与组件控制，不假设总CFSG
T03|分量|平衡与标准分量约化|T02,R02|centralizer奇核商分量的提升、balance、standard-form及显式例外
T04|分量|经典与交错分量识别|T03,K00,A02|覆盖交错/经典分量、弱闭性及几何重建所有参数
T05|分量|例外Lie分量识别|T03,K00,A02|覆盖例外与扭曲Lie分量及坏特征例外
T06|分量|散在分量与例外识别|T03,K00,S01,S02,S03,S04,S05,S06,S07|每个散在分量及混合/例外局部构形回到名单
T07|桥接|非D且非C2残余约化|T01,T02,F04,K00|证明残余矛盾或给出有限明列例外并逐个识别
T08|特征2|pushing-up与局部模|F03,R01,T01,I00,K00|大2子群、parabolic系统、quadratic/FF模与amalgam约束
T09|特征2|quasithin完整分支|T08|QTKE接口、两卷全部所需局部结构及简单QTKE识别，显式处理例外
T10|特征2|高宽度几何与识别|T08,A02|rank1/2与高秩几何、连通/单连通、Curtis-Tits/Phan及识别
T11|特征2|特征2型散在与例外|T08,K00,S01,S02,S03,S04,S05,S06,S07|几何分支以外逐个局部构形识别及quasithin外例外
D00|总路由|原始谓词覆盖|F01,F02,O02|阿贝尔/奇偶/2秩/D/C2/e2的逻辑分支穷尽
D01|总路由|文献假设桥接|D00,T03,T07,T08|D、C2、宽度与所用各文献假设之间的确切蕴含和例外覆盖
Z00|收口|K-proper单群分类|D01,T00,T04,T05,T06,T09,T10,T11,N00|在完整显式K-proper假设下产出具体CFSGIndex与MulEquiv
Z01|收口|无条件阶归纳|Z00,I00,C00|对Nat.card强归纳消去所有K假设，得到Type零分类
Z02|收口|固定目标与全名单核验|Z01,K00,E01|全宇宙ClassificationStatement、逐项Finite/IsSimpleGroup及完整公理审计
'''
packages=[]
for line in DATA.strip().splitlines():
 i,stream,title,deps,accept=line.split('|')
 packages.append(dict(id=i,stream=stream,title=title,depends_on=deps.split(',') if deps else [],acceptance=accept,status='proposed_unverified',owner_role=stream+'负责人'))
families = {
 'A':'L01','twistedA':'L01','B':'L02','C':'L01','D':'L02','twistedD':'L02',
 'E6':'L03','E7':'L03','E8':'L03','F4':'L03','G2':'L03','twistedE6':'L04','trialityD4':'L04',
 'suzuki':'L05','reeG2':'L05','reeF4':'L05','tits':'L05'}
sporadics={
 'M11':'S01','M12':'S01','M22':'S01','M23':'S01','M24':'S01',
 'J1':'S02','J2':'S02','J3':'S02','J4':'S02','Co1':'S03','Co2':'S03','Co3':'S03','Suz':'S03',
 'HS':'S04','McL':'S04','He':'S04','Ru':'S04','ONan':'S04','Ly':'S04',
 'Fi22':'S05','Fi23':'S05','Fi24Prime':'S05','HN':'S06','Th':'S06','B':'S06','M':'S07'}
ledger=dict(schema_version=1,evidence_level='project-design; not theorem-level dependency graph or Lean verification',target='TauCeti.ClassificationStatement',mathlib_rev='b63f6e8a68d220e3b3bc4f3792bb53650d375f24',tauceti_rev='6e0c6acab5f4c6f42e5f5bab9bd5e4e84f74c380',packages=packages,lie_family_owner=families,sporadic_owner=sporadics)
(ROOT/'design/obligations.json').write_text(json.dumps(ledger,ensure_ascii=False,indent=2)+'\n')
print(f'Wrote {len(packages)} proposed work packages; 17 Lie constructors; 26 sporadics.')
