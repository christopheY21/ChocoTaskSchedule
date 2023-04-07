import java.util.ArrayList;
import java.util.Arrays;
import java.util.Scanner;
import java.util.Vector;
import java.util.stream.IntStream;

import org.apache.pdfbox.pdmodel.font.encoding.ZapfDingbatsEncoding;
import org.chocosolver.solver.Model;
import org.chocosolver.solver.Solution;
import org.chocosolver.solver.Solver;
import org.chocosolver.solver.constraints.Constraint;
import org.chocosolver.solver.expression.discrete.relational.UnCReExpression;
import org.chocosolver.solver.search.loop.monitors.IMonitorSolution;
import org.chocosolver.solver.search.strategy.Search;
import org.chocosolver.solver.variables.BoolVar;
import org.chocosolver.solver.variables.IntVar;
import org.chocosolver.solver.variables.Task;
import org.chocosolver.util.tools.ArrayUtils;




public class Choco {
	public static boolean contains(final int[] arr, final int key) {
		for (int i=0 ;i <arr.length ; i++) {
			if(arr[i]==key) {
				return true;
			}
		}
	    return false;
	}
	public static void main(String[] args) {
		// TODO Auto-generated method stub
		Scanner scanner = new Scanner(System.in);
		//TASKS
		int l = scanner.nextInt()+1; // The number of tasks
		int taskNumber = l;
		int[] size = new int[l]; // The size of each task
		int[] data = new int[l]; // The output data size of each task
		int[][] Ai = new int[l][]; // The affinitive machines for each task
		l = l-1;
		System.out.println("Number of tasks : "+l);
		//Tasklist get
		// ID	SIZE	DATA_SIZE	NmachineAF	IDAF1	IDAF
		
		for (int i = 0; i < l; i++) {
			int id = scanner.nextInt();//ID
		    size[id] = scanner.nextInt(); //SIZE
		    data[id] = scanner.nextInt();//DATA_SIZE
		    int k = scanner.nextInt(); //nMachinesAF
		    Ai[id] = new int[k];
		    for (int j = 0; j < k; j++) {
	      		Ai[id][j] = scanner.nextInt();
		    }
		}
		//MACHINES
		l = scanner.nextInt()+1;// The number of machines
		int numberOfMachines = l;
		int[] power = new int[l];
		power[0] = 0;
		for (int i =0 ; i < l -1 ; i++) {
			int id = scanner.nextInt();
			power[id] = scanner.nextInt();
		}
		//DISKS
		l = scanner.nextInt()+1;// The number of disks
		int numberOfDisks = l;
		int[] speed = new int[l];
		int[] capacity = new int[l];
		speed[0]=0;
		capacity[0]=0;
		for(int i =0 ; i < l-1 ;i++) {
			int id = scanner.nextInt();
			speed[id] = scanner.nextInt();
			capacity[id] = scanner.nextInt();
			
		}
		//Data dependencies
		int numberDataDependencies = scanner.nextInt();
		//j'ai la flemme d'utiliser un vecteur et il y a beaucoup de mémoire gache ici
		Vector<Integer>[] PREDdata = new Vector[taskNumber];// The data-dependent tasks for each task
		for (int i = 0; i < taskNumber; i++) {
			  PREDdata[i] = new Vector<Integer>();
		}
		for(int i=0; i< numberDataDependencies;i++) {
			int id1 = scanner.nextInt();
			int id2 = scanner.nextInt();
			PREDdata[id2].add(id1);
		}
		int numberTaskDependencies = scanner.nextInt();
		Vector<Integer>[] PREDtask = new Vector[taskNumber];// The task-dependent tasks for each task
		for (int i = 0; i < taskNumber; i++) {
			  PREDtask[i] = new Vector<Integer>();
		}
		
		for(int i=0; i< numberTaskDependencies;i++) {
			int id1 = scanner.nextInt();
			int id2 = scanner.nextInt();
			PREDtask[id2].add(id1);
		}
		//DUMMY INDEX 0 
		// ID	SIZE	DATA_SIZE	NmachineAF	IDAF1	IDAF
		size[0]=0;
		data[0]=0;
		Ai[0] = new int[1];
		Ai[0][0] = 0;
		System.out.println("Number of machines: "+numberOfMachines);
		System.out.println("Number of disks: " + numberOfDisks);
//------------------------------------------------------------------------------------------------------------------------------------------------
		System.out.println("Finished loading");
		//Solving the problem with choco solver
		/*
		 * xi: the starting time of task i. This can be an integer variable with domain [0, ∞).
		 * yi: the machine on which task i is run. This can be an integer variable with domain [1, n], where n is the number of machines.
		 * zi: the disk where the data of task i is stored. This can be an integer variable with domain [1, m], where m is the number of disks.
		 * 
		 * Processing phase
		 * ai = xi
		 * bi = ai + sum j predData upperbound (data(j)/speed(zj))
		 * ci = bi + upperbound(size(i)/power(yi))
		 * di = ci + upperdbound(data(i)/speed(zi))
		 * 1- Starting time
		 * 2- reading data from other tasks
		 * 3- executing the task
		 * 4- storing data
		 */
		// Create a new Choco model
		Model model = new Model("Task Scheduling");
		// Create an array to store the variables for each task
		IntVar[] x = new IntVar[taskNumber];
		IntVar[] y = new IntVar[taskNumber];
		IntVar[] z = new IntVar[taskNumber];
		for (int i = 0; i < taskNumber; i++) {
			  // xi: the starting time of task i. This can be an integer variable with domain [0, ∞).
			  x[i] = model.intVar("x" + i, 0,500);
			  // yi: the machine on which task i is run.
			  y[i] = model.intVar("y" + i, Ai[i]);
			  //System.out.println(Arrays.toString(Ai[i]));
			  // zi: the disk where the data of task i is stored. This can be an integer variable with domain [1, m], where m is the number of disks.
			  z[i] = model.intVar("z" + i, 0, numberOfDisks);
			}
		// Compute sum pred dataSpeed for precedor
		// intermediary variable ∑j∈PREDdata(i)⌈data(j)/speed(zj)⌉
		//predDataSpeed(task,Disk)
		//[[0,1],
		// [0,2]]
		int[][] predDataSpeed = new int[taskNumber][];
		
		for (int i=0; i< taskNumber ; i++) {
			predDataSpeed[i] = new int[numberOfDisks];
			for (int k =0; k < numberOfDisks ; k++) {
				int sum = 0;
				for (int j=0 ; j< PREDdata[i].size();j++) {
					if(speed[k]!=0) {
						sum += (int) Math.ceil(data[PREDdata[i].get(j)]/speed[k]);
					}
				}
				predDataSpeed[i][k] = sum;
			}
			//System.out.println(Arrays.toString(predDataSpeed[i]));
		}
		
		
		//Compute possible value for size/power -> iter through all machines possible for i
		//⌈size(i)/power(yi)⌉
		//sizePower(task machine)
		// AI give affinitive machine of a task
		/*
		int[][] sizePower = new int[taskNumber][];
		for (int i=0; i< taskNumber ; i++) {
			
			sizePower[i] = new int[Ai[i].length];
			for (int k =0 ; k < Ai[i].length ; k++) {
				if(power[Ai[i][k]]!=0) {
					sizePower[i][k] = (int) Math.ceil(size[i]/power[Ai[i][k]]);
				}
			}
			System.out.println(Arrays.toString(sizePower[i]));
		}
		*/

		int[][] sizePower = new int[taskNumber][numberOfMachines];
		for (int i=0 ; i< taskNumber ; i++) {
			
			for (int k =0 ; k< numberOfMachines ; k++) {
				//if(Arrays.asList(Ai[i]).contains((int) k)) {//affinitive machines
				if(contains(Ai[i],k)) {
					if(power[k]!=0) {
						sizePower[i][k] = (int) Math.ceil(size[i]/power[k]);
					}
				}
				else {// non affinitive machines
					sizePower[i][k] = 99999;
				}
			}
			//System.out.println(Arrays.toString(sizePower[i]));

		}
		//Compute possible value for data/speed
		//⌈data(i)/speed(zi)⌉
		int[][] dataSpeed = new int[taskNumber][numberOfDisks];
		for (int i =0 ; i <taskNumber ; i++) {
			for( int k=0 ; k< numberOfDisks; k++) {
				if(speed[k]!=0) {
					//System.out.println("Data:"+data[i] + " Speed :"+speed[k]);
					dataSpeed[i][k] = (int) Math.ceil(data[i]/speed[k]);
				}
				else {
					dataSpeed[i][k] = 99999;
				}
			}
			//System.out.println(Arrays.toString(dataSpeed[i]));
		}
		
		
		//Create annex variables
		IntVar[] a = new IntVar[taskNumber];
		IntVar[] b = new IntVar[taskNumber];
		IntVar[] dummyB = new IntVar[taskNumber];
		IntVar[] c = new IntVar[taskNumber];
		IntVar[] dummyC = new IntVar[taskNumber];
		IntVar[] d = new IntVar[taskNumber];
		IntVar[] dummyD = new IntVar[taskNumber];
		IntVar[] height = new IntVar[taskNumber];
		IntVar[] width = new IntVar[taskNumber];
		IntVar[] taskI = new IntVar[taskNumber];
		IntVar[] capacityTask = new IntVar[taskNumber];
		for (int i = 0; i< taskNumber ; i++) {
			/*a[i] = model.intVar("a" + i, 0,50000);
			b[i] = model.intVar("b"+i,0,50000);
			//height Constraint
*/			taskI[i] = model.intVar("taskI"+i,i);
			//capacity Constraint
			capacityTask[i] = model.intVar("capacityI"+i,0,100000);
			model.element(capacityTask[i], capacity, z[i]);
			// ai
			a[i] = model.intVar("a" + i, 0,50000);
			// bi
			//dummyB[i] = model.intVar("B"+i,predDataSpeed[i]);
			dummyB[i] = model.intVar("B"+i,0,50000);

			//System.out.println(Arrays.toString(predDataSpeed[i]));
			//System.out.println(dummyB[i].toString());
			b[i] = model.intVar("b"+i,0,50000);
			model.element(dummyB[i], predDataSpeed[i], z[i]).post();

			// ci
			//dummyC[i] =model.intVar("C"+i,sizePower[i]);
			dummyC[i] =model.intVar("C"+i,0,50000);
			model.element(dummyC[i], sizePower[i], y[i]).post();

			
			c[i] =model.intVar("c"+i,0,50000);

			//di 
			//dummyD[i] =model.intVar("D"+i,dataSpeed[i]);
			dummyD[i] =model.intVar("D"+i,0,50000);
			model.element(dummyD[i], dataSpeed[i], z[i]).post();

			d[i] =model.intVar("d"+i,0,50000);
			
			height[i] = model.intVar("heigth"+i,0,500000);
			model.element(height[i], data, taskI[i]).post();

			width[i] = model.intVar("width"+i,-500000,5000000);
			//WIDTHd-a
			//HEIGHT
		}
		
		//define channeling constraint element

		model.arithm(x[0],"=",0).post();//ai
		model.arithm(d[0],"=",0).post();//ai
		//model.arithm(z[1],"=",2).post();//ai

		//model.arithm(z[6],"=",2).post();//ai

		//define ai,bi,ci,di constraint 
		for (int i=0 ; i< taskNumber ; i++) {
			model.arithm(x[i],"=",a[i]).post();//ai constraint
			model.arithm(a[i],"+", dummyB[i],"=",b[i]).post(); //bi constraint
			//TODO : add all dummyB for PREDTASK
			model.arithm(b[i], "+", dummyC[i],"=",c[i]).post();//ci constraint
			model.arithm(c[i], "+", dummyD[i],"=",d[i]).post();//di constraint
			model.arithm(d[i], "-", a[i],"=",width[i]).post();//width constraint

			
		}
		//defines constraint schedule

		
		model.diffN(
				  a,
				  y,
				  width,
				  IntStream.range(0, taskNumber).mapToObj(i -> model.intVar(1)).toArray(IntVar[]::new),
				  true).post();	
		//define intvar[] each disk
		// For each disk find which task is assigned to this disk and write their data
		//model.sum(vars, op, x).post(); //vars = tasks[] data assigned to disk
		//define vars
		//TROUVER LES TASKS ASSIGNER A UN DISK
		
		IntVar[][] diskHeight = new IntVar[numberOfDisks][taskNumber];
		for(int i=0 ; i<numberOfDisks;i++) {
			for(int j =0 ; j<taskNumber;j++) {
				
				diskHeight[i][j]= model.intVar("diskHeight"+i+":"+j, 0,10000);
				model.ifThen(model.arithm(z[j],"=",i),
						model.element(diskHeight[i][j], data, taskI[j]));
				model.ifThen(model.arithm(z[j],"!=",i),
						model.arithm(diskHeight[i][j],"=",0));
						

				
			}
		}
		for(int i=0 ; i<numberOfDisks;i++) {
			model.sum(diskHeight[i], "<=", capacity[i]).post();
		}
		
		
		//model.cumulative(x, width, height, capacity);;

		
		for (int i = 0; i < taskNumber; i++) {
			// No preemption: for each pair of tasks i and j such that yi = yj, the two intervals (ai, di) and (aj, dj) cannot have any overlaps.
			// This can be expressed as a constraint of the form ai + di ≤ aj or aj + dj ≤ ai, depending on which task starts first.
			  for (int j = i+1; j < taskNumber; j++) {
				  /*
				  BoolVar iBeforej = model.arithm(a[i], "+", d[i], "<=", a[j]).reify();
				  BoolVar jBeforei = model.arithm(a[j], "+", d[j], "<=", a[i]).reify();
				  y[i].eq(y[j]).imp(iBeforej.or(jBeforei)).post();
*/
					  
			  }
			
			
			// Task dependencies: for each task j ∈ PREDtask(i), task i cannot start until j finishes its execution.
			// This can be expressed as a constraint of the form ai ≥ cj.
			//TODO : Note that if i is scheduled on the same machine with j, then it still needs to wait for j to complete storing its data.
			for (int j : PREDtask[i]) {
				model.arithm(a[i], ">=", c[j]).post();
			}
			// Data dependencies: for each task j ∈ PREDdata(i), task i cannot start until j finishes storing its data.
			// This can be expressed as a constraint of the form ai ≥ dj.
			for (int j : PREDdata[i]) {
				model.arithm(a[i], ">=", d[j]).post();
			}
			// Affinity of machines: yi ∈ Ai, where Ai is the list of affinitive machines for task i.
			// This can be expressed as a constraint of the form yi = a for some a ∈ Ai.
			//int[] affinitive = Ai[i];
			//model.member(variables[i][1], affinitive).post();
			
			//DISK CAPACITY
			

			
		}
		IntVar makespan = model.intVar("maxD",0,5000);
		model.max(makespan, d).post();
		// Solution
		Solver solver = model.getSolver();
		
		solver.plugMonitor((IMonitorSolution) () -> {
			for (int i = 0; i < taskNumber; i++) {
				//PRINT X, Y ,Z 
				System.out.println("i:"+i+" ,xi:"+x[i].getValue()
					+" ,yi:"+y[i].getValue()
							+" ,zi: "+z[i].getValue()
							+" ,ai: "+a[i].getValue()
							+" ,bi: "+b[i].getValue()
							+" ,ci: "+c[i].getValue()
							+" ,di: "+d[i].getValue()
							//+" ,width : "+width[i].getValue()
							//+" ,max : "+maximal.getValue()
							);
			}
			/*
			for(int i=0 ; i<numberOfDisks;i++) {
				for(int j =0 ; j<taskNumber;j++) {
					System.out.println(
							"disk:"+i+",task:"+j+" ->"+diskHeight[i][j].getValue()+"taskI:"+taskI[j].getValue());
				}
			}
			*/
		});
		//solver.limitTime("2s");
		//test
		solver.findOptimalSolution(makespan, false);
		/*

		for (int i = 0; i < taskNumber; i++) {
			//PRINT X, Y ,Z 
			System.out.println("i:"+i+" ,xi:"+x[i].getValue()
				+" ,yi:"+y[i].getValue()
						+" ,zi: "+z[i].getValue()
						+" ,ai: "+a[i].getValue()
						+" ,bi: "+b[i].getValue()
						+" ,ci: "+c[i].getValue()
						+" ,di: "+d[i].getValue()
						+" ,width : "+width[i].getValue()
						//+" ,max : "+maximal.getValue()
						);
		}

		*/
		System.out.println(Arrays.toString(data));

		System.out.println("ENDPROGRAM");
	}
	/*Example input
	6
	1 40 6 2 1 2
	2 20 6 2 1 2
	3 96 10 2 1 2
	4 20 6 2 1 2
	5 60 0 2 1 2
	6 20 0 1 1
	2
	1 1
	2 2
	2
	1 1 30
	2 2 17
	8
	1 2
	1 3
	1 4
	2 4
	2 5
	3 5
	3 6
	4 6
	1
	1 5
	 */

}
