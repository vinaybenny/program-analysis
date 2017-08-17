import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import soot.Body;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.jimple.toolkits.callgraph.ReachableMethods;
import soot.toolkits.graph.BriefBlockGraph;
import soot.toolkits.graph.BriefUnitGraph;
import soot.toolkits.graph.DirectedGraph;
import soot.util.Chain;

/* 
Author: Vinay Benny
Description: Implemented as part of program analysis (CS5218) Assignment 1.
Purpose: Class  for Interprocedural Taint Analysis	
Date : 25 Mar 2013
*/

public class InterTaintAnalysis {

/* Data structure skeleton that stores inter-procedural analysis information*/	
public class MethodInformation{
	Body methodBody;
	String methodName;
	HashSet preSet;
	HashSet genSet;
	HashSet killSet;
	String printOut;
	MethodInformation(Body methodBody, String methodName, 
			HashSet preSet, HashSet genSet, HashSet killSet,String printOut){	
		this.methodBody=methodBody;
		this.methodName=methodName;
		this.preSet=preSet;
		this.genSet=genSet;
		this.killSet=killSet;
		this.printOut=printOut;
	}


}

/* This hashmap maps the method signature to the related detailed method information*/
public static HashMap<String, MethodInformation> methodInfo = new HashMap<String, MethodInformation>();

/*This keeps a list of methods encountered during program execution for later iteration and obtaining the inter-
 * procedural fix point*/
public static HashSet<String> methodList= new HashSet<String>();


	public InterTaintAnalysis(Chain<SootClass> classes) {
		
		Body mainBody = null;
		String name = new String();
		
		/*Set up the Global Dictionary for methods*/
		Iterator iter = classes.iterator();
		while(iter.hasNext())
		{
			SootClass sc = (SootClass) iter.next();
			Iterator <SootMethod> siter= 	sc.methodIterator();			

			while(siter.hasNext())
			{
				SootMethod sm = (SootMethod) siter.next(); 
				Body methBody = sm.getActiveBody();
				name = sm.getSignature();
				String temp = "";
				soot.Type returnType = sm.getReturnType();
				List parameterType = sm.getParameterTypes();
				SootClass methClass = sm.getDeclaringClass();
				HashSet<String> params= new HashSet<String>();				
							
				MethodInformation methodDtls = new MethodInformation(methBody,name,new HashSet(),new HashSet(),new HashSet(),
						temp);
												
				methodInfo.put(name, methodDtls);
				
			}
		}
		
		Iterator iter2 = classes.iterator();
		while(iter2.hasNext())
		{
			SootClass sc = (SootClass) iter2.next();			
			Iterator <SootMethod> siter= 	sc.methodIterator();			
			
			while(siter.hasNext())
			{
				SootMethod sm = (SootMethod)siter.next();
				
				/* If current method is main, get details for beginning the iteration*/	
				if(sm.isMain())
				{
					mainBody = sm.getActiveBody();
					Integer paramCount = sm.getParameterCount();
					Integer loopCount = 0;
					
					while (loopCount < paramCount)
					{
						HashSet<String> mainParams= new HashSet<String>();
						mainParams.add("@parameter"+loopCount);						
						methodInfo.get(sm.getSignature()).preSet.addAll(mainParams);
						loopCount++;
					}
					methodList.add(sm.getSignature().toString());
					
				}
			}
		}
		
		

		HashMap<String, MethodInformation> initInfo = new HashMap<String, MethodInformation>();
		HashMap<String, MethodInformation> finalInfo = new HashMap<String, MethodInformation>();
		Integer i = 1;
		
		String mainName = methodList.iterator().next().toString();
		
		/*Iterate through the worklist of methods until the taint information of all methods become the same, ie,
		 * fix point is reached*/
		Integer loopCounterupper = 0;
		do{
			System.out.println("Higher Level Iteration: "+loopCounterupper);
			
			/* Add the main method's signature to the global method worklist*/
			if(!(methodList.contains(mainName)))
			{
				methodList.add(mainName);
			}
			
			/* Make the previous final taint info, the current iteration's initial info for fix point checking*/
			initInfo = new HashMap(copyHashmap(finalInfo));
			
			/* Iterate through the worklist  */
			while(!(methodList.size()==0))
			{
				String methSign = methodList.iterator().next().toString();
				methodList.remove(methSign);

				IntraTaintAnalysis iTa = new IntraTaintAnalysis(new BriefUnitGraph(methodInfo.get(methSign).methodBody));
			}
			
			/*Set finalInfo equal to the methodInfo after each iteration through the entire method worklist.
			 * This will be required for fixpoint at interprocedural level */
			finalInfo = new HashMap<String, MethodInformation>(copyHashmap(methodInfo));
		
			i = compareHashMaps(initInfo, finalInfo);
			loopCounterupper++;
		} while( i==1 );
		
		
		/* Print out the method signatures */
		System.out.println("\t\tInter-Procedural Analysis-Fix Point reached\n\t\tMethod Signature Details\n\t\t-----------------------\n");
		for(Entry<String,MethodInformation> entry : methodInfo.entrySet())
		{
			MethodInformation maint = methodInfo.get(entry.getKey());
			
			String maintName = maint.methodName;
			System.out.println("Method : "+maintName);
			System.out.println("Preset : "+maint.preSet);
			System.out.println("Genset : "+maint.genSet+"\n");	
			System.out.println("Killset : "+maint.killSet+"\n");
		}
		/* Print out intra-procedural results */
		
		
	}

	/* Method that performs comparison between 2 hashmaps*/
	private Integer compareHashMaps(Map<String, MethodInformation> initInfo,
			Map<String, MethodInformation> finalInfo) {

		Integer returnVal = 0;

		for (String key : finalInfo.keySet())
		{
			MethodInformation x = finalInfo.get(key);

			if(initInfo.containsKey(key))
			{
				MethodInformation y = initInfo.get(key);								
				if (!(x.preSet.equals(y.preSet) && x.genSet.equals(y.genSet) && x.killSet.equals(y.killSet)))
				{
					returnVal = 1;
				}
			}
			else 
			{
				returnVal = 1;
			}
			
		}
			    
		return returnVal;
	}

	/*HashMap lookup for getting method info by method name*/ 
	public static MethodInformation findMethod (String methodName)
	{		
		MethodInformation mI = methodInfo.get(methodName);
		return mI;
	}
	
	/* Deep copy for hashmaps*/
	public  HashMap<String, MethodInformation> copyHashmap(HashMap<String, MethodInformation> initial)
	{
		HashMap<String, MethodInformation> temp = new HashMap<String, MethodInformation>();
		
		Iterator it = initial.entrySet().iterator();
		while (it.hasNext())
		{
			Map.Entry<String, MethodInformation> mapentry= (Map.Entry<String, MethodInformation>) it.next();
			String key = new String(mapentry.getKey());
			MethodInformation val = mapentry.getValue();
			HashSet<String> pre = new HashSet<String>(val.preSet);
			HashSet<String> gen = new HashSet<String>(val.genSet);
			HashSet<String> kill = new HashSet<String>(val.killSet);
			String mname = new String(val.methodName);
			String print = new String(val.printOut);			
			
			MethodInformation methx = new MethodInformation(val.methodBody, mname,
					pre, gen, kill,print);
			temp.put(key, methx);
		}
		
		
		return temp;
		
	}
}
