import java.util.Map;

import soot.Body;
import soot.BodyTransformer;
import soot.PackManager;
import soot.SootMethod;
import soot.Transform;
import soot.options.Options;
import soot.toolkits.graph.BriefBlockGraph;
import soot.toolkits.graph.BriefUnitGraph;

/**
 * Feb 8, 2013
 * @author Zuo Zhiqiang
 */
public class IntraMainDriver {
	public static void main(String[] args) {
		PackManager.v().getPack("jtp").add(new Transform("jtp.myTransform", new BodyTransformer(){

			@Override
			protected void internalTransform(Body b, String phaseName, Map options) {
				// TODO Auto-generated method stub
				SootMethod m = b.getMethod();
				System.out.println(m.getName());
				System.out.println("----------------------------------------------------");
				//your taint analysis will print out all the data flow information
				IntraTaintAnalysis analysis = new IntraTaintAnalysis(new BriefUnitGraph(b));
				System.out.println("----------------------------------------------------\n\n\n");
			}
			
		}));
		
		Options.v().setPhaseOption("bb", "enabled:false");
		Options.v().setPhaseOption("gb", "enabled:false");
		Options.v().setPhaseOption("tag", "enabled:false");
		Options.v().setPhaseOption("jap", "enabled:false");
		Options.v().setPhaseOption("jb", "use-original-names:true");
		Options.v().set_keep_line_number(true);
		
		soot.Main.main(args);
	}

}
