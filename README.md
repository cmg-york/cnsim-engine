# Consensus Network Simulator - Simulation Engine (CNSim-Engine)

CNSim-Engine is the object-oriented framework that lies at the core of CNSim, a toolset for simulating blockchain consensus networks. The engine offers a set of abstractions, objects, and routines for quickly developing and running event-driven simulators of individual consensus networks. As such it is meant to be used as a library of *instantiating projects* to use in order to analyze specific protocols.

## Installation
At this stage, the easiest way to instantiate CNSim-Engine assets is through installation to your local Maven repository:

1. In the `cnsim-engine` directory just do:

```
mvn install
```

this will compile and install the library to your local Maven repo.

2. In your instantiating code then (e.g. `cnsim-bitcoin`) just add this to your `pom.xml`

```
<dependencies>

  ...

  <dependency>
    <groupId>ca.yorku.cmg</groupId>
    <artifactId>cnsim-engine</artifactId>
    <version>0.0.2-SNAPSHOT</version>
  </dependency>

</dependencies>
```

Ensure that the version is the same as in the `pom.xml` at the root of this repository.

## Documentation
* A conceptual overview of CNSim-Engine can be found here \[under construction\].
* A complete example of how CNSim has been instantiated to simulate Bitcoin can be found here \[under construction \].
* Complete API reference can be found here \[under construction \].

## Clarification on License
LGPL license adoption is intended to allow reuse of the framework for instantiating both proprietary and open-source (of any license) consensus protocol simulators. You can, for example create a proprietary tool for simulating a popular consensus protocol using this library a derivative of which you can maintain and distribute. 

However, while the instantiating code per se can be proprietary, the derivatives and re-distributions of the CNSim-Engine assets themselves need to follow the open source GPL provisions, chiefly that the code is open and under the same license. 

The LICENSE text contains the authoritative licensing information.

