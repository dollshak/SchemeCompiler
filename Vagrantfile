# -*- mode: ruby -*-
def utop_autocomplete_config(machine)
  machine.vm.provision "file", source: "vagrant.d/.lambda-term-inputrc", destination: "$HOME/lambda-term-inputrc"
end

Vagrant.configure(2) do |config|
   config.vm.provider "virtualbox" do |vb|
     vb.memory = "2048"
   end
   
   config.vm.define "cs-linux" do |machine|
     machine.vm.box = "Neowizard/cs-linux"
     machine.ssh.insert_key = true
     machine.vm.synced_folder ".", "/home/vagrant/compiler"
     utop_autocomplete_config machine
  end

end
