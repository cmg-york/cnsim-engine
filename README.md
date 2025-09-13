# Consensus Network Simulator - Simulation Engine (CNSim-Engine)

CNSim-Engine is the object-oriented framework that lies at the core of CNSim, a toolset for simulating blockchain consensus networks. The engine offers a set of abstractions, objects, and routines for quickly developing and running event-driven simulators of individual consensus networks. As such it is meant to be used as a library of *instantiating projects* to use in order to analyze specific protocols.
## Installation
At this stage, the easiest way to access the CNSim-Engine assets is through:
1. Downloading the JAR to your local project,
2. Adding it to the project instantiating the framework. For a maven project, assuming the JAR is named `cnsim-engine-0.0.1-SNAPSHOT.jar` and is placed under the `/lib` directory of the instantiating project, the following dependency can be added inside the dependencies:
```
<dependency>
	<groupId>ca.yorku.cmg.cnsim</groupId>
	<artifactId>cnsim-engine</artifactId>
	<version>0.0.1-SNAPSHOT</version>
	<scope>system</scope>
	<systemPath>${project.basedir}/lib/cnsim-engine-0.0.1-SNAPSHOT.jar</systemPath>
</dependency>
```

## Documentation
* A conceptual overview of CNSim-Engine can be found here \[under construction\].
* A complete example of how CNSim has been instantiated to simulate Bitcoin can be found here \[under construction \].
* Complete API reference can be found here \[under construction \].

## Clarification on License
LGPL license adoption is intended to allow reuse of the framework for instantiating both proprietary and open-source (of any license) consensus protocol simulators. You can, for example create a proprietary tool for simulating a popular consensus protocol using this library a derivative of which you can maintain and distribute. 

However, while the instantiating code per se can be proprietary, the derivatives and re-distributions of the CNSim-Engine assets themselves need to follow the open source GPL provisions, chiefly that the code is open and under the same license. 

The LICENSE text contains the authoritative licensing information.

