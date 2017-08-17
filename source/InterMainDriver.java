

import java.util.Map;

import soot.PackManager;
import soot.Scene;
import soot.SceneTransformer;
import soot.SootClass;
import soot.Transform;
import soot.options.Options;
import soot.util.Chain;

/**
 * Feb 8, 2013
 * @author Zuo Zhiqiang
 */
public class InterMainDriver {
	public static void main(String[] args) {
		PackManager.v().getPack("wjtp").add(new Transform("wjtp.myTransform", new SceneTransformer(){

			@Override
			protected void internalTransform(String phaseName, Map options) {
				// TODO Auto-generated method stub
				Chain<SootClass> classes = Scene.v().getApplicationClasses();
				//you should implement the inter-procedural taint analysis as class InterTaintAnalysis
				InterTaintAnalysis analysis = new InterTaintAnalysis(classes);
			}
			
		}));
		
		Options.v().set_whole_program(true);
		Options.v().setPhaseOption("wjpp", "enabled:false");
		Options.v().setPhaseOption("wspp", "enabled:false");
		Options.v().setPhaseOption("cg", "enabled:false");
		Options.v().setPhaseOption("wjap", "enabled:false");
		
		Options.v().setPhaseOption("bb", "enabled:false");
		Options.v().setPhaseOption("gb", "enabled:false");
		Options.v().setPhaseOption("tag", "enabled:false");
		Options.v().setPhaseOption("jap", "enabled:false");
		Options.v().setPhaseOption("jb", "use-original-names:true");
		Options.v().set_keep_line_number(true);
		
		//args is a list of all the application classes analyzed
		soot.Main.main(args);
	}

}
