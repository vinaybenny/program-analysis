

import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import soot.Body;
import soot.BodyTransformer;
import soot.PackManager;
import soot.Transform;
import soot.Unit;
import soot.jimple.IfStmt;
import soot.jimple.LookupSwitchStmt;
import soot.jimple.TableSwitchStmt;
import soot.options.Options;
import soot.toolkits.graph.Block;
import soot.toolkits.graph.BriefBlockGraph;
import soot.toolkits.graph.BriefUnitGraph;
import soot.toolkits.graph.DirectedGraph;
import soot.toolkits.graph.pdg.HashMutablePDG;
import soot.toolkits.graph.pdg.IRegion;
import soot.toolkits.graph.pdg.PDGNode;

/**
 * @author Zuo Zhiqiang
 *
 */
public class CDA {
	final DirectedGraph cfg;
	final Map<Unit, Unit> CDMap;//maintain only direct control dependency
	final Map<Unit, HashSet<Unit>> CDSMap;//maintain both direct and indirect control dependency
	
	
	public CDA(DirectedGraph cfg) {
		this.cfg = cfg;
		this.CDMap = new HashMap<Unit, Unit>();
		this.CDSMap = new HashMap<Unit, HashSet<Unit>>();
		
		calculateControlDependency();
	}


	private void calculateControlDependency(){
		/* first step: get direct control dependency information */
		HashMutablePDG pdg = new HashMutablePDG((BriefUnitGraph) cfg);
		List<Object> nodes = pdg.getNodes(); // a list of all the pdg nodes: PDGNode
		for(Iterator<PDGNode> it = pdg.iterator(); it.hasNext();){
			PDGNode controlNode = it.next();
			if(controlNode.getType() == PDGNode.Type.CFGNODE){
				//if it's CFGNODE, cast this pdg node to a block
				Block bk = (Block) controlNode.getNode();
				Unit tail = bk.getTail();
				//check whether the tail unit of the block contains controlling expression: ifStmt and SwitchStmt
				if(tail instanceof IfStmt || tail instanceof TableSwitchStmt || tail instanceof LookupSwitchStmt){
					for(Object o: nodes){
						PDGNode node = (PDGNode) o;
						//check whether node is control dependent on controlNode 
						if(pdg.dependentOn(node, controlNode)){
							IRegion region = (IRegion) node.getNode();
							//all the units in this region are control dependent on tail 
							for(Unit u: region.getUnits()){
								CDMap.put(u, tail);
							}
						}
					}
				}
			}
		}
		
		/* second step: calculate both indirect and direct control dependency maintained by CDSMap */
		for(Unit key: CDMap.keySet()){
			CDSMap.put(key, new HashSet<Unit>());
			Unit u = key;
			while(CDMap.containsKey(u)){
				u = CDMap.get(u);
				CDSMap.get(key).add(u);
			}
		}
	}
	
	
	public Map<Unit, Unit> getCDMap() {
		return CDMap;
	}

	public Map<Unit, HashSet<Unit>> getCDSMap() {
		return CDSMap;
	}


	//for testing and debugging
//	public static void main(String[] args) {
//		PackManager.v().getPack("jtp").add(new Transform("jtp.myTransform", new BodyTransformer(){
//
//			@Override
//			protected void internalTransform(Body b, String phaseName, Map options) {
//				System.out.println(b.getMethod().getName());
//				System.out.println("----------------------------------------------------");
//				System.out.println(new BriefBlockGraph(new BriefUnitGraph(b)).toString());
//				System.out.println("----------------------------------------------------\n\n\n");
//				CDAnalysis cda = new CDAnalysis(new BriefUnitGraph(b));
//				for(Unit unit: cda.CDMap.keySet()){
//					System.out.println(unit.toString() + ":\t" + cda.CDMap.get(unit).toString());
//				}
//				System.out.println("=================");
//				for(Unit unit: cda.CDSMap.keySet()){
//					System.out.println(unit.toString() + ":\t" + cda.CDSMap.get(unit).toString());
//				}
//				System.out.println("----------------------------------------------------\n\n\n");
//				System.out.println("=================");
//			}
//			
//		}));
//		
//		Options.v().setPhaseOption("bb", "enabled:false");
//		Options.v().setPhaseOption("gb", "enabled:false");
//		Options.v().setPhaseOption("tag", "enabled:false");
//		Options.v().setPhaseOption("jap", "enabled:false");
//		Options.v().setPhaseOption("jb", "use-original-names:true");
//		Options.v().set_keep_line_number(true);
//		Options.v().set_output_format(Options.output_format_jimple);
//		
//		//args is a list of all the application classes analyzed
//		soot.Main.main(args);
//	}
	

}
